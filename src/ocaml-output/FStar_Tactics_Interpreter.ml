open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (tac_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let refl =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reflect FStar_Parser_Const.tac_effect_lid))
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    FStar_Syntax_Util.mk_app refl [(t, FStar_Pervasives_Native.None)]
  
let (maybe_reflect :
  Prims.bool ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun reflect  -> fun t  -> if reflect then tac_reflect t else t 
let mk_tactic_interpretation_0 :
  'r .
    Prims.bool ->
      'r FStar_Tactics_Basic.tac ->
        'r FStar_Syntax_Embeddings.embedder ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun embed_r  ->
        fun t_r  ->
          fun nm  ->
            fun psc  ->
              fun args  ->
                match args with
                | (embedded_state,uu____115)::[] ->
                    let uu____132 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state
                       in
                    FStar_Util.bind_opt uu____132
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____148  ->
                              let uu____149 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____150 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.print2 "Reached %s, args are: %s\n"
                                uu____149 uu____150);
                         (let res =
                            let uu____152 =
                              FStar_TypeChecker_Normalize.psc_range psc  in
                            let uu____153 = FStar_Tactics_Basic.run t ps1  in
                            let uu____156 =
                              FStar_Tactics_Embedding.embed_result embed_r
                                t_r
                               in
                            uu____156 uu____152 uu____153  in
                          let uu____170 = maybe_reflect reflect res  in
                          FStar_Pervasives_Native.Some uu____170))
                | uu____175 ->
                    failwith "Unexpected application of tactic primitive"
  
let mk_tactic_interpretation_1 :
  'a 'r .
    Prims.bool ->
      ('a -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'r FStar_Syntax_Embeddings.embedder ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun psc  ->
                fun args  ->
                  match args with
                  | (a,uu____252)::(embedded_state,uu____254)::[] ->
                      let uu____281 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____281
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____296  ->
                                let uu____297 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____298 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____297
                                  uu____298);
                           (let uu____299 = unembed_a a  in
                            FStar_Util.bind_opt uu____299
                              (fun a1  ->
                                 let res =
                                   let uu____313 = t a1  in
                                   FStar_Tactics_Basic.run uu____313 ps1  in
                                 let uu____316 =
                                   let uu____319 =
                                     let uu____322 =
                                       FStar_TypeChecker_Normalize.psc_range
                                         psc
                                        in
                                     let uu____323 =
                                       FStar_Tactics_Embedding.embed_result
                                         embed_r t_r
                                        in
                                     uu____323 uu____322 res  in
                                   FStar_All.pipe_left
                                     (maybe_reflect reflect) uu____319
                                    in
                                 FStar_Pervasives_Native.Some uu____316)))
                  | uu____343 ->
                      let uu____344 =
                        let uu____345 = FStar_Ident.string_of_lid nm  in
                        let uu____346 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____345 uu____346
                         in
                      failwith uu____344
  
let mk_tactic_interpretation_1_env :
  'a 'r .
    Prims.bool ->
      (FStar_TypeChecker_Normalize.psc -> 'a -> 'r FStar_Tactics_Basic.tac)
        ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'r FStar_Syntax_Embeddings.embedder ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun psc  ->
                fun args  ->
                  match args with
                  | (a,uu____428)::(embedded_state,uu____430)::[] ->
                      let uu____457 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____457
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____472  ->
                                let uu____473 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____474 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____473
                                  uu____474);
                           (let uu____475 = unembed_a a  in
                            FStar_Util.bind_opt uu____475
                              (fun a1  ->
                                 let res =
                                   let uu____489 = t psc a1  in
                                   FStar_Tactics_Basic.run uu____489 ps1  in
                                 let uu____492 =
                                   let uu____495 =
                                     let uu____498 =
                                       FStar_TypeChecker_Normalize.psc_range
                                         psc
                                        in
                                     let uu____499 =
                                       FStar_Tactics_Embedding.embed_result
                                         embed_r t_r
                                        in
                                     uu____499 uu____498 res  in
                                   FStar_All.pipe_left
                                     (maybe_reflect reflect) uu____495
                                    in
                                 FStar_Pervasives_Native.Some uu____492)))
                  | uu____519 ->
                      let uu____520 =
                        let uu____521 = FStar_Ident.string_of_lid nm  in
                        let uu____522 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____521 uu____522
                         in
                      failwith uu____520
  
let mk_tactic_interpretation_2 :
  'a 'b 'r .
    Prims.bool ->
      ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'r FStar_Syntax_Embeddings.embedder ->
              FStar_Syntax_Syntax.typ ->
                FStar_Ident.lid ->
                  FStar_TypeChecker_Normalize.psc ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun embed_r  ->
            fun t_r  ->
              fun nm  ->
                fun psc  ->
                  fun args  ->
                    match args with
                    | (a,uu____619)::(b,uu____621)::(embedded_state,uu____623)::[]
                        ->
                        let uu____660 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____660
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____675  ->
                                  let uu____676 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____677 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____676
                                    uu____677);
                             (let uu____678 = unembed_a a  in
                              FStar_Util.bind_opt uu____678
                                (fun a1  ->
                                   let uu____688 = unembed_b b  in
                                   FStar_Util.bind_opt uu____688
                                     (fun b1  ->
                                        let res =
                                          let uu____702 = t a1 b1  in
                                          FStar_Tactics_Basic.run uu____702
                                            ps1
                                           in
                                        let uu____705 =
                                          let uu____708 =
                                            let uu____711 =
                                              FStar_TypeChecker_Normalize.psc_range
                                                psc
                                               in
                                            let uu____712 =
                                              FStar_Tactics_Embedding.embed_result
                                                embed_r t_r
                                               in
                                            uu____712 uu____711 res  in
                                          FStar_All.pipe_left
                                            (maybe_reflect reflect) uu____708
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____705))))
                    | uu____732 ->
                        let uu____733 =
                          let uu____734 = FStar_Ident.string_of_lid nm  in
                          let uu____735 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____734 uu____735
                           in
                        failwith uu____733
  
let mk_tactic_interpretation_3 :
  'a 'b 'c 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'c FStar_Syntax_Embeddings.unembedder ->
              'r FStar_Syntax_Embeddings.embedder ->
                FStar_Syntax_Syntax.typ ->
                  FStar_Ident.lid ->
                    FStar_TypeChecker_Normalize.psc ->
                      FStar_Syntax_Syntax.args ->
                        FStar_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun unembed_c  ->
            fun embed_r  ->
              fun t_r  ->
                fun nm  ->
                  fun psc  ->
                    fun args  ->
                      match args with
                      | (a,uu____852)::(b,uu____854)::(c,uu____856)::
                          (embedded_state,uu____858)::[] ->
                          let uu____905 =
                            FStar_Tactics_Embedding.unembed_proofstate
                              embedded_state
                             in
                          FStar_Util.bind_opt uu____905
                            (fun ps  ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____920  ->
                                    let uu____921 =
                                      FStar_Ident.string_of_lid nm  in
                                    let uu____922 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state
                                       in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n" uu____921
                                      uu____922);
                               (let uu____923 = unembed_a a  in
                                FStar_Util.bind_opt uu____923
                                  (fun a1  ->
                                     let uu____933 = unembed_b b  in
                                     FStar_Util.bind_opt uu____933
                                       (fun b1  ->
                                          let uu____943 = unembed_c c  in
                                          FStar_Util.bind_opt uu____943
                                            (fun c1  ->
                                               let res =
                                                 let uu____957 = t a1 b1 c1
                                                    in
                                                 FStar_Tactics_Basic.run
                                                   uu____957 ps1
                                                  in
                                               let uu____960 =
                                                 let uu____963 =
                                                   let uu____966 =
                                                     FStar_TypeChecker_Normalize.psc_range
                                                       psc
                                                      in
                                                   let uu____967 =
                                                     FStar_Tactics_Embedding.embed_result
                                                       embed_r t_r
                                                      in
                                                   uu____967 uu____966 res
                                                    in
                                                 FStar_All.pipe_left
                                                   (maybe_reflect reflect)
                                                   uu____963
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____960)))))
                      | uu____987 ->
                          let uu____988 =
                            let uu____989 = FStar_Ident.string_of_lid nm  in
                            let uu____990 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____989 uu____990
                             in
                          failwith uu____988
  
let mk_tactic_interpretation_5 :
  'a 'b 'c 'd 'e 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'c FStar_Syntax_Embeddings.unembedder ->
              'd FStar_Syntax_Embeddings.unembedder ->
                'e FStar_Syntax_Embeddings.unembedder ->
                  'r FStar_Syntax_Embeddings.embedder ->
                    FStar_Syntax_Syntax.typ ->
                      FStar_Ident.lid ->
                        FStar_TypeChecker_Normalize.psc ->
                          FStar_Syntax_Syntax.args ->
                            FStar_Syntax_Syntax.term
                              FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun unembed_c  ->
            fun unembed_d  ->
              fun unembed_e  ->
                fun embed_r  ->
                  fun t_r  ->
                    fun nm  ->
                      fun psc  ->
                        fun args  ->
                          match args with
                          | (a,uu____1147)::(b,uu____1149)::(c,uu____1151)::
                              (d,uu____1153)::(e,uu____1155)::(embedded_state,uu____1157)::[]
                              ->
                              let uu____1224 =
                                FStar_Tactics_Embedding.unembed_proofstate
                                  embedded_state
                                 in
                              FStar_Util.bind_opt uu____1224
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1239  ->
                                        let uu____1240 =
                                          FStar_Ident.string_of_lid nm  in
                                        let uu____1241 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state
                                           in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1240 uu____1241);
                                   (let uu____1242 = unembed_a a  in
                                    FStar_Util.bind_opt uu____1242
                                      (fun a1  ->
                                         let uu____1252 = unembed_b b  in
                                         FStar_Util.bind_opt uu____1252
                                           (fun b1  ->
                                              let uu____1262 = unembed_c c
                                                 in
                                              FStar_Util.bind_opt uu____1262
                                                (fun c1  ->
                                                   let uu____1272 =
                                                     unembed_d d  in
                                                   FStar_Util.bind_opt
                                                     uu____1272
                                                     (fun d1  ->
                                                        let uu____1282 =
                                                          unembed_e e  in
                                                        FStar_Util.bind_opt
                                                          uu____1282
                                                          (fun e1  ->
                                                             let res =
                                                               let uu____1296
                                                                 =
                                                                 t a1 b1 c1
                                                                   d1 e1
                                                                  in
                                                               FStar_Tactics_Basic.run
                                                                 uu____1296
                                                                 ps1
                                                                in
                                                             let uu____1299 =
                                                               let uu____1302
                                                                 =
                                                                 let uu____1305
                                                                   =
                                                                   FStar_TypeChecker_Normalize.psc_range
                                                                    psc
                                                                    in
                                                                 let uu____1306
                                                                   =
                                                                   FStar_Tactics_Embedding.embed_result
                                                                    embed_r
                                                                    t_r
                                                                    in
                                                                 uu____1306
                                                                   uu____1305
                                                                   res
                                                                  in
                                                               FStar_All.pipe_left
                                                                 (maybe_reflect
                                                                    reflect)
                                                                 uu____1302
                                                                in
                                                             FStar_Pervasives_Native.Some
                                                               uu____1299)))))))
                          | uu____1326 ->
                              let uu____1327 =
                                let uu____1328 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____1329 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1328 uu____1329
                                 in
                              failwith uu____1327
  
let (step_from_native_step :
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Normalize.primitive_step)
  =
  fun s  ->
    {
      FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
      FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
      FStar_TypeChecker_Normalize.strong_reduction_ok =
        (s.FStar_Tactics_Native.strong_reduction_ok);
      FStar_TypeChecker_Normalize.requires_binder_substitution = false;
      FStar_TypeChecker_Normalize.interpretation =
        (fun psc  -> fun args  -> s.FStar_Tactics_Native.tactic psc args)
    }
  
let rec (primitive_steps :
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____1381  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]
         in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation =
          (fun psc  -> fun args  -> interpretation nm1 psc args)
      }  in
    let native_tactics = FStar_Tactics_Native.list_all ()  in
    let native_tactics_steps =
      FStar_List.map step_from_native_step native_tactics  in
    let mktac0 r name f e_r tr =
      mk1 name (Prims.parse_int "1")
        (mk_tactic_interpretation_0 false f e_r tr)
       in
    let mktac1 a r name f u_a e_r tr =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 false f u_a e_r tr)
       in
    let mktac2 a b r name f u_a u_b e_r tr =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 false f u_a u_b e_r tr)
       in
    let mktac3 a b c r name f u_a u_b u_c e_r tr =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 false f u_a u_b u_c e_r tr)
       in
    let mktac5 a b c d e r name f u_a u_b u_c u_d u_e e_r tr =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 false f u_a u_b u_c u_d u_e e_r tr)
       in
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____1869)::[] ->
          let uu____1886 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1886
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1894 =
                 let uu____1895 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1896 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1895
                   uu____1896
                  in
               FStar_Pervasives_Native.Some uu____1894)
      | uu____1897 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____1901 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1901;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1914)::[] ->
          let uu____1931 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1931
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1939 =
                 let uu____1940 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1941 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1940
                   uu____1941
                  in
               FStar_Pervasives_Native.Some uu____1939)
      | uu____1942 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____1946 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1946;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1963)::[] ->
          let uu____1980 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1980
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1993 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2010)::(r,uu____2012)::[] ->
          let uu____2039 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2039
            (fun ps1  ->
               let uu____2045 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____2045
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2053 =
                      let uu____2054 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____2054 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2053))
      | uu____2055 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let set_proofstate_range_step =
      let nm =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation =
          set_proofstate_range_interp
      }  in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      }  in
    let put1 rng t =
      let uu___60_2069 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___60_2069.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___60_2069.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____2076 =
      let uu____2079 =
        mktac2 () () () "__fail"
          (fun a434  ->
             fun a435  ->
               (Obj.magic (fun uu____2081  -> FStar_Tactics_Basic.fail)) a434
                 a435) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____2082 =
        let uu____2085 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____2086 =
          let uu____2089 =
            let uu____2090 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a436  ->
                 fun a437  ->
                   (Obj.magic (fun uu____2096  -> FStar_Tactics_Basic.trytac))
                     a436 a437) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____2090)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2103 =
            let uu____2106 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Basic.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____2107 =
              let uu____2110 =
                let uu____2111 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____2118 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____2111) uu____2118
                 in
              let uu____2125 =
                let uu____2128 =
                  let uu____2129 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "__norm"
                    (fun a438  -> (Obj.magic FStar_Tactics_Basic.norm) a438)
                    (Obj.magic uu____2129)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____2138 =
                  let uu____2141 =
                    let uu____2142 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step
                       in
                    mktac3 () () () () "__norm_term_env"
                      (fun a439  ->
                         fun a440  ->
                           fun a441  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a439 a440 a441)
                      (Obj.magic FStar_Reflection_Basic.unembed_env)
                      (Obj.magic uu____2142)
                      (Obj.magic FStar_Reflection_Basic.unembed_term)
                      (Obj.magic FStar_Reflection_Basic.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2151 =
                    let uu____2154 =
                      let uu____2155 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "__norm_binder_type"
                        (fun a442  ->
                           fun a443  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a442 a443) (Obj.magic uu____2155)
                        (Obj.magic FStar_Reflection_Basic.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2164 =
                      let uu____2167 =
                        mktac2 () () () "__rename_to"
                          (fun a444  ->
                             fun a445  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a444
                                 a445)
                          (Obj.magic FStar_Reflection_Basic.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit
                         in
                      let uu____2168 =
                        let uu____2171 =
                          mktac1 () () "__binder_retype"
                            (fun a446  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a446)
                            (Obj.magic FStar_Reflection_Basic.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2172 =
                          let uu____2175 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2176 =
                            let uu____2179 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2180 =
                              let uu____2183 =
                                mktac1 () () "__clear"
                                  (fun a447  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a447)
                                  (Obj.magic
                                     FStar_Reflection_Basic.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit
                                 in
                              let uu____2184 =
                                let uu____2187 =
                                  mktac1 () () "__rewrite"
                                    (fun a448  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a448)
                                    (Obj.magic
                                       FStar_Reflection_Basic.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                let uu____2188 =
                                  let uu____2191 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2192 =
                                    let uu____2195 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2196 =
                                      let uu____2199 =
                                        mktac3 () () () () "__t_exact"
                                          (fun a449  ->
                                             fun a450  ->
                                               fun a451  ->
                                                 (Obj.magic
                                                    FStar_Tactics_Basic.t_exact)
                                                   a449 a450 a451)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Basic.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit
                                         in
                                      let uu____2200 =
                                        let uu____2203 =
                                          mktac1 () () "__apply"
                                            (fun a452  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a452)
                                            (Obj.magic
                                               FStar_Reflection_Basic.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____2204 =
                                          let uu____2207 =
                                            mktac1 () () "__apply_raw"
                                              (fun a453  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a453)
                                              (Obj.magic
                                                 FStar_Reflection_Basic.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____2208 =
                                            let uu____2211 =
                                              mktac1 () () "__apply_lemma"
                                                (fun a454  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a454)
                                                (Obj.magic
                                                   FStar_Reflection_Basic.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____2212 =
                                              let uu____2215 =
                                                let uu____2216 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a455  ->
                                                     fun a456  ->
                                                       fun a457  ->
                                                         fun a458  ->
                                                           fun a459  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2225
                                                                    ->
                                                                   fun
                                                                    uu____2226
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a455 a456 a457
                                                               a458 a459)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____2216)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2233 =
                                                let uu____2236 =
                                                  mktac1 () ()
                                                    "__set_options"
                                                    (fun a460  ->
                                                       (Obj.magic
                                                          FStar_Tactics_Basic.set_options)
                                                         a460)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.unembed_string)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.embed_unit)
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                let uu____2237 =
                                                  let uu____2240 =
                                                    mktac2 () () () "__seq"
                                                      (fun a461  ->
                                                         fun a462  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.seq)
                                                             a461 a462)
                                                      (Obj.magic
                                                         (unembed_tactic_0'
                                                            FStar_Syntax_Embeddings.unembed_unit))
                                                      (Obj.magic
                                                         (unembed_tactic_0'
                                                            FStar_Syntax_Embeddings.unembed_unit))
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.embed_unit)
                                                      FStar_Syntax_Syntax.t_unit
                                                     in
                                                  let uu____2241 =
                                                    let uu____2244 =
                                                      mktac1 () () "__tc"
                                                        (fun a463  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a463)
                                                        (Obj.magic
                                                           FStar_Reflection_Basic.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Basic.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____2245 =
                                                      let uu____2248 =
                                                        mktac1 () ()
                                                          "__unshelve"
                                                          (fun a464  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a464)
                                                          (Obj.magic
                                                             FStar_Reflection_Basic.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____2249 =
                                                        let uu____2252 =
                                                          mktac2 () () ()
                                                            "__unquote"
                                                            (fun a465  ->
                                                               fun a466  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a465 a466)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Basic.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____2253 =
                                                          let uu____2256 =
                                                            mktac1 () ()
                                                              "__prune"
                                                              (fun a467  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a467)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____2257 =
                                                            let uu____2260 =
                                                              mktac1 () ()
                                                                "__addns"
                                                                (fun a468  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a468)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____2261 =
                                                              let uu____2264
                                                                =
                                                                mktac1 () ()
                                                                  "__print"
                                                                  (fun a469 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun x 
                                                                    ->
                                                                    FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                    FStar_Tactics_Basic.ret
                                                                    ())) a469)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____2269
                                                                =
                                                                let uu____2272
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "__dump"
                                                                    (
                                                                    fun a470 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a470)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____2273
                                                                  =
                                                                  let uu____2276
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__dump1"
                                                                    (fun a471
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a471)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                  let uu____2277
                                                                    =
                                                                    let uu____2280
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a472
                                                                     ->
                                                                    fun a473 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a472 a473)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2281
                                                                    =
                                                                    let uu____2284
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2285
                                                                    =
                                                                    let uu____2288
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2289
                                                                    =
                                                                    let uu____2292
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2293
                                                                    =
                                                                    let uu____2296
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2297
                                                                    =
                                                                    let uu____2300
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2301
                                                                    =
                                                                    let uu____2304
                                                                    =
                                                                    let uu____2305
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2312
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "__cases"
                                                                    (fun a474
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a474)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2305)
                                                                    uu____2312
                                                                     in
                                                                    let uu____2319
                                                                    =
                                                                    let uu____2322
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2323
                                                                    =
                                                                    let uu____2326
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2327
                                                                    =
                                                                    let uu____2330
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2331
                                                                    =
                                                                    let uu____2334
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2335
                                                                    =
                                                                    let uu____2338
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2339
                                                                    =
                                                                    let uu____2342
                                                                    =
                                                                    let uu____2343
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__uvar_env"
                                                                    (fun a475
                                                                     ->
                                                                    fun a476 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a475 a476)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2343)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2352
                                                                    =
                                                                    let uu____2355
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__unify"
                                                                    (fun a477
                                                                     ->
                                                                    fun a478 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a477 a478)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2356
                                                                    =
                                                                    let uu____2359
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "__launch_process"
                                                                    (fun a479
                                                                     ->
                                                                    fun a480 
                                                                    ->
                                                                    fun a481 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a479 a480
                                                                    a481)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_string)
                                                                    FStar_Syntax_Syntax.t_string
                                                                     in
                                                                    [uu____2359;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step]
                                                                     in
                                                                    uu____2355
                                                                    ::
                                                                    uu____2356
                                                                     in
                                                                    uu____2342
                                                                    ::
                                                                    uu____2352
                                                                     in
                                                                    uu____2338
                                                                    ::
                                                                    uu____2339
                                                                     in
                                                                    uu____2334
                                                                    ::
                                                                    uu____2335
                                                                     in
                                                                    uu____2330
                                                                    ::
                                                                    uu____2331
                                                                     in
                                                                    uu____2326
                                                                    ::
                                                                    uu____2327
                                                                     in
                                                                    uu____2322
                                                                    ::
                                                                    uu____2323
                                                                     in
                                                                    uu____2304
                                                                    ::
                                                                    uu____2319
                                                                     in
                                                                    uu____2300
                                                                    ::
                                                                    uu____2301
                                                                     in
                                                                    uu____2296
                                                                    ::
                                                                    uu____2297
                                                                     in
                                                                    uu____2292
                                                                    ::
                                                                    uu____2293
                                                                     in
                                                                    uu____2288
                                                                    ::
                                                                    uu____2289
                                                                     in
                                                                    uu____2284
                                                                    ::
                                                                    uu____2285
                                                                     in
                                                                    uu____2280
                                                                    ::
                                                                    uu____2281
                                                                     in
                                                                  uu____2276
                                                                    ::
                                                                    uu____2277
                                                                   in
                                                                uu____2272 ::
                                                                  uu____2273
                                                                 in
                                                              uu____2264 ::
                                                                uu____2269
                                                               in
                                                            uu____2260 ::
                                                              uu____2261
                                                             in
                                                          uu____2256 ::
                                                            uu____2257
                                                           in
                                                        uu____2252 ::
                                                          uu____2253
                                                         in
                                                      uu____2248 ::
                                                        uu____2249
                                                       in
                                                    uu____2244 :: uu____2245
                                                     in
                                                  uu____2240 :: uu____2241
                                                   in
                                                uu____2236 :: uu____2237  in
                                              uu____2215 :: uu____2233  in
                                            uu____2211 :: uu____2212  in
                                          uu____2207 :: uu____2208  in
                                        uu____2203 :: uu____2204  in
                                      uu____2199 :: uu____2200  in
                                    uu____2195 :: uu____2196  in
                                  uu____2191 :: uu____2192  in
                                uu____2187 :: uu____2188  in
                              uu____2183 :: uu____2184  in
                            uu____2179 :: uu____2180  in
                          uu____2175 :: uu____2176  in
                        uu____2171 :: uu____2172  in
                      uu____2167 :: uu____2168  in
                    uu____2154 :: uu____2164  in
                  uu____2141 :: uu____2151  in
                uu____2128 :: uu____2138  in
              uu____2110 :: uu____2125  in
            uu____2106 :: uu____2107  in
          uu____2089 :: uu____2103  in
        uu____2085 :: uu____2086  in
      uu____2079 :: uu____2082  in
    FStar_List.append uu____2076
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term -> 'Ab FStar_Tactics_Basic.tac
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state  ->
           let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
           let tm =
             let uu____2382 =
               let uu____2383 =
                 let uu____2384 =
                   let uu____2385 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2385  in
                 [uu____2384]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2383  in
             uu____2382 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____2392 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____2392
            then
              let uu____2393 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2393
            else ());
           (let result =
              let uu____2396 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2396 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____2400 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2400
             then
               let uu____2401 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2401
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2446 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2446
                   (fun uu____2450  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2473 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2473
                   (fun uu____2477  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2490 =
                   let uu____2495 =
                     let uu____2496 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2496
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2495)  in
                 FStar_Errors.raise_error uu____2490
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2505 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
        uu____2505

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2561  ->
             match uu____2561 with
             | (r,uu____2581,uv,uu____2583,ty,rng) ->
                 let uu____2586 =
                   let uu____2587 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____2588 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2587 uu____2588 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2586, rng)) is
         in
      match errs with
      | [] -> ()
      | (e,msg,r)::tl1 ->
          (FStar_Tactics_Basic.dump_proofstate ps
             "failing due to uninstantiated implicits";
           FStar_Errors.add_errors tl1;
           FStar_Errors.raise_error (e, msg) r)
  
let (run_tactic_on_typ :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Tactics_Basic.goal Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun tactic  ->
    fun env  ->
      fun typ  ->
        (let uu____2637 = FStar_ST.op_Bang tacdbg  in
         if uu____2637
         then
           let uu____2657 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2657
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         FStar_Errors.stop_if_err ();
         (let tau =
            unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1  in
          let uu____2664 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____2664 with
          | (env1,uu____2678) ->
              let env2 =
                let uu___61_2684 = env1  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___61_2684.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___61_2684.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___61_2684.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___61_2684.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___61_2684.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___61_2684.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___61_2684.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___61_2684.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___61_2684.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp = false;
                  FStar_TypeChecker_Env.effects =
                    (uu___61_2684.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___61_2684.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___61_2684.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___61_2684.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___61_2684.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___61_2684.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___61_2684.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___61_2684.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___61_2684.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___61_2684.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___61_2684.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___61_2684.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___61_2684.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___61_2684.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___61_2684.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___61_2684.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___61_2684.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___61_2684.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___61_2684.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___61_2684.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___61_2684.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___61_2684.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___61_2684.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___61_2684.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___61_2684.FStar_TypeChecker_Env.dep_graph)
                }  in
              let uu____2685 =
                FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ  in
              (match uu____2685 with
               | (ps,w) ->
                   ((let uu____2699 = FStar_ST.op_Bang tacdbg  in
                     if uu____2699
                     then
                       let uu____2719 = FStar_Syntax_Print.term_to_string typ
                          in
                       FStar_Util.print1 "Running tactic with goal = %s\n"
                         uu____2719
                     else ());
                    (let uu____2721 =
                       FStar_Util.record_time
                         (fun uu____2731  -> FStar_Tactics_Basic.run tau ps)
                        in
                     match uu____2721 with
                     | (res,ms) ->
                         ((let uu____2745 = FStar_ST.op_Bang tacdbg  in
                           if uu____2745
                           then
                             let uu____2765 = FStar_Util.string_of_int ms  in
                             FStar_Util.print1
                               "Tactic ran in %s milliseconds\n" uu____2765
                           else ());
                          (match res with
                           | FStar_Tactics_Result.Success (uu____2773,ps1) ->
                               ((let uu____2776 = FStar_ST.op_Bang tacdbg  in
                                 if uu____2776
                                 then
                                   let uu____2796 =
                                     FStar_Syntax_Print.term_to_string w  in
                                   FStar_Util.print1
                                     "Tactic generated proofterm %s\n"
                                     uu____2796
                                 else ());
                                FStar_List.iter
                                  (fun g  ->
                                     let uu____2803 =
                                       FStar_Tactics_Basic.is_irrelevant g
                                        in
                                     if uu____2803
                                     then
                                       let uu____2804 =
                                         FStar_TypeChecker_Rel.teq_nosmt
                                           g.FStar_Tactics_Types.context
                                           g.FStar_Tactics_Types.witness
                                           FStar_Syntax_Util.exp_unit
                                          in
                                       (if uu____2804
                                        then ()
                                        else
                                          (let uu____2806 =
                                             let uu____2807 =
                                               FStar_Syntax_Print.term_to_string
                                                 g.FStar_Tactics_Types.witness
                                                in
                                             FStar_Util.format1
                                               "Irrelevant tactic witness does not unify with (): %s"
                                               uu____2807
                                              in
                                           failwith uu____2806))
                                     else ())
                                  (FStar_List.append
                                     ps1.FStar_Tactics_Types.goals
                                     ps1.FStar_Tactics_Types.smt_goals);
                                (let g =
                                   let uu___62_2810 =
                                     FStar_TypeChecker_Rel.trivial_guard  in
                                   {
                                     FStar_TypeChecker_Env.guard_f =
                                       (uu___62_2810.FStar_TypeChecker_Env.guard_f);
                                     FStar_TypeChecker_Env.deferred =
                                       (uu___62_2810.FStar_TypeChecker_Env.deferred);
                                     FStar_TypeChecker_Env.univ_ineqs =
                                       (uu___62_2810.FStar_TypeChecker_Env.univ_ineqs);
                                     FStar_TypeChecker_Env.implicits =
                                       (ps1.FStar_Tactics_Types.all_implicits)
                                   }  in
                                 let g1 =
                                   let uu____2812 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env2 g
                                      in
                                   FStar_All.pipe_right uu____2812
                                     FStar_TypeChecker_Rel.resolve_implicits_tac
                                    in
                                 report_implicits ps1
                                   g1.FStar_TypeChecker_Env.implicits;
                                 ((FStar_List.append
                                     ps1.FStar_Tactics_Types.goals
                                     ps1.FStar_Tactics_Types.smt_goals), w)))
                           | FStar_Tactics_Result.Failed (s,ps1) ->
                               ((let uu____2819 =
                                   let uu____2820 =
                                     FStar_TypeChecker_Normalize.psc_subst
                                       ps1.FStar_Tactics_Types.psc
                                      in
                                   FStar_Tactics_Types.subst_proof_state
                                     uu____2820 ps1
                                    in
                                 FStar_Tactics_Basic.dump_proofstate
                                   uu____2819 "at the time of failure");
                                (let uu____2821 =
                                   let uu____2826 =
                                     FStar_Util.format1
                                       "user tactic failed: %s" s
                                      in
                                   (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                     uu____2826)
                                    in
                                 FStar_Errors.raise_error uu____2821
                                   typ.FStar_Syntax_Syntax.pos)))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2836 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2840 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2844 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2893 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2929 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2979 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3017 . 'Auu____3017 -> 'Auu____3017 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3036 = FStar_Syntax_Util.head_and_args t  in
        match uu____3036 with
        | (hd1,args) ->
            let uu____3073 =
              let uu____3086 =
                let uu____3087 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3087.FStar_Syntax_Syntax.n  in
              (uu____3086, args)  in
            (match uu____3073 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3100))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3163 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3163 with
                       | (gs,uu____3171) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3178 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3178 with
                       | (gs,uu____3186) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3237 =
                        let uu____3244 =
                          let uu____3247 =
                            let uu____3248 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3248
                             in
                          [uu____3247]  in
                        (FStar_Syntax_Util.t_true, uu____3244)  in
                      Simplified uu____3237
                  | Both  ->
                      let uu____3259 =
                        let uu____3272 =
                          let uu____3275 =
                            let uu____3276 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3276
                             in
                          [uu____3275]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3272)  in
                      Dual uu____3259
                  | Neg  -> Simplified (assertion, []))
             | uu____3297 -> Unchanged t)
  
let explode :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___59_3377  ->
      match uu___59_3377 with
      | Unchanged t -> let uu____3383 = f t  in Unchanged uu____3383
      | Simplified (t,gs) ->
          let uu____3390 = let uu____3397 = f t  in (uu____3397, gs)  in
          Simplified uu____3390
      | Dual (tn,tp,gs) ->
          let uu____3407 =
            let uu____3416 = f tn  in
            let uu____3417 = f tp  in (uu____3416, uu____3417, gs)  in
          Dual uu____3407
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3471 = f t1 t2  in Unchanged uu____3471
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3483 = let uu____3490 = f t1 t2  in (uu____3490, gs)
               in
            Simplified uu____3483
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3504 = let uu____3511 = f t1 t2  in (uu____3511, gs)
               in
            Simplified uu____3504
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3530 =
              let uu____3537 = f t1 t2  in
              (uu____3537, (FStar_List.append gs1 gs2))  in
            Simplified uu____3530
        | uu____3540 ->
            let uu____3549 = explode x  in
            (match uu____3549 with
             | (n1,p1,gs1) ->
                 let uu____3567 = explode y  in
                 (match uu____3567 with
                  | (n2,p2,gs2) ->
                      let uu____3585 =
                        let uu____3594 = f n1 n2  in
                        let uu____3595 = f p1 p2  in
                        (uu____3594, uu____3595, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3585))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3660 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3660
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3703  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3737 =
              let uu____3738 = FStar_Syntax_Subst.compress t  in
              uu____3738.FStar_Syntax_Syntax.n  in
            match uu____3737 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3750 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3750 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3774 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3774 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3792;
                   FStar_Syntax_Syntax.vars = uu____3793;_},(p,uu____3795)::
                 (q,uu____3797)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3837 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3837
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3840 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3840 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3846 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3846.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3850;
                   FStar_Syntax_Syntax.vars = uu____3851;_},(p,uu____3853)::
                 (q,uu____3855)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3895 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3895
                   in
                let xq =
                  let uu____3897 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3897
                   in
                let r1 =
                  let uu____3899 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3899 p  in
                let r2 =
                  let uu____3901 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3901 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3904,Unchanged uu____3905) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3915 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3915.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3918 ->
                     let uu____3923 = explode r1  in
                     (match uu____3923 with
                      | (pn,pp,gs1) ->
                          let uu____3941 = explode r2  in
                          (match uu____3941 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3962 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3963 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3962
                                   uu____3963
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4015  ->
                       fun r  ->
                         match uu____4015 with
                         | (a,q) ->
                             let r' = traverse f pol e a  in
                             comb2
                               (fun a1  -> fun args1  -> (a1, q) :: args1) r'
                               r) args (tpure [])
                   in
                comb2
                  (fun hd2  ->
                     fun args1  -> FStar_Syntax_Syntax.Tm_app (hd2, args1))
                  r0 r1
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____4133 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4133 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4167  ->
                            match uu____4167 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4181 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___63_4205 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___63_4205.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___63_4205.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4181 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4225 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4225.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4271 = traverse f pol e t1  in
                let uu____4276 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4276 uu____4271
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___64_4314 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___64_4314.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___64_4314.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4321 =
                f pol e
                  (let uu___65_4325 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___65_4325.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___65_4325.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4321
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___66_4335 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___66_4335.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___66_4335.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4336 = explode rp  in
              (match uu____4336 with
               | (uu____4345,p',gs') ->
                   Dual
                     ((let uu___67_4359 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___67_4359.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___67_4359.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
  
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t
         in
      FStar_Syntax_Util.un_squash tn
  
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_Options.optionstate)
        FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun env  ->
    fun goal  ->
      (let uu____4394 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4394);
      (let uu____4415 = FStar_ST.op_Bang tacdbg  in
       if uu____4415
       then
         let uu____4435 =
           let uu____4436 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4436
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4437 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4435
           uu____4437
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4466 =
         let uu____4473 = traverse by_tactic_interp Pos env goal  in
         match uu____4473 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4491 -> failwith "no"  in
       match uu____4466 with
       | (t',gs) ->
           ((let uu____4513 = FStar_ST.op_Bang tacdbg  in
             if uu____4513
             then
               let uu____4533 =
                 let uu____4534 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4534
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4535 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4533 uu____4535
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4582  ->
                    fun g  ->
                      match uu____4582 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4627 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____4627 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4630 =
                                  let uu____4631 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty
                                     in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4631
                                   in
                                failwith uu____4630
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4634 = FStar_ST.op_Bang tacdbg  in
                            if uu____4634
                            then
                              let uu____4654 = FStar_Util.string_of_int n1
                                 in
                              let uu____4655 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4654 uu____4655
                            else ());
                           (let gt' =
                              let uu____4658 =
                                let uu____4659 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4659
                                 in
                              FStar_TypeChecker_Util.label uu____4658
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____4674 = s1  in
             match uu____4674 with
             | (uu____4695,gs1) ->
                 let uu____4713 =
                   let uu____4720 = FStar_Options.peek ()  in
                   (env, t', uu____4720)  in
                 uu____4713 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4731 =
        let uu____4732 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4732  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4731 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4733 =
      let uu____4734 =
        let uu____4735 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4736 =
          let uu____4739 = FStar_Syntax_Syntax.as_arg a  in [uu____4739]  in
        uu____4735 :: uu____4736  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4734  in
    uu____4733 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4752 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____4752);
        (let uu____4772 =
           let uu____4779 = reify_tactic tau  in
           run_tactic_on_typ uu____4779 env typ  in
         match uu____4772 with
         | (gs,w) ->
             let uu____4786 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4790 =
                      let uu____4791 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4791  in
                    Prims.op_Negation uu____4790) gs
                in
             if uu____4786
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "synthesis left open goals") typ.FStar_Syntax_Syntax.pos
             else w)
  