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
           (FStar_Const.Const_reflect FStar_Parser_Const.effect_TAC_lid))
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
  fun uu____1415  ->
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
      | (ps,uu____1903)::[] ->
          let uu____1920 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1920
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1928 =
                 let uu____1929 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1930 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1929
                   uu____1930
                  in
               FStar_Pervasives_Native.Some uu____1928)
      | uu____1931 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____1935 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1935;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1948)::[] ->
          let uu____1965 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1965
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1973 =
                 let uu____1974 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1975 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1974
                   uu____1975
                  in
               FStar_Pervasives_Native.Some uu____1973)
      | uu____1976 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____1980 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1980;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1997)::[] ->
          let uu____2014 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2014
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2027 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2044)::(r,uu____2046)::[] ->
          let uu____2073 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2073
            (fun ps1  ->
               let uu____2079 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____2079
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2087 =
                      let uu____2088 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____2088 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2087))
      | uu____2089 ->
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
      let uu___58_2103 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___58_2103.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___58_2103.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____2110 =
      let uu____2113 =
        mktac2 () () () "__fail"
          (fun a438  ->
             fun a439  ->
               (Obj.magic (fun uu____2115  -> FStar_Tactics_Basic.fail)) a438
                 a439) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____2116 =
        let uu____2119 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____2120 =
          let uu____2123 =
            let uu____2124 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a440  ->
                 fun a441  ->
                   (Obj.magic (fun uu____2130  -> FStar_Tactics_Basic.trytac))
                     a440 a441) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____2124)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2137 =
            let uu____2140 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Embeddings.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____2141 =
              let uu____2144 =
                let uu____2145 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____2152 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____2145) uu____2152
                 in
              let uu____2159 =
                let uu____2162 =
                  let uu____2163 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "__norm"
                    (fun a442  -> (Obj.magic FStar_Tactics_Basic.norm) a442)
                    (Obj.magic uu____2163)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____2172 =
                  let uu____2175 =
                    let uu____2176 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step
                       in
                    mktac3 () () () () "__norm_term_env"
                      (fun a443  ->
                         fun a444  ->
                           fun a445  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a443 a444 a445)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_env)
                      (Obj.magic uu____2176)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_term)
                      (Obj.magic FStar_Reflection_Embeddings.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2185 =
                    let uu____2188 =
                      let uu____2189 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "__norm_binder_type"
                        (fun a446  ->
                           fun a447  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a446 a447) (Obj.magic uu____2189)
                        (Obj.magic FStar_Reflection_Embeddings.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2198 =
                      let uu____2201 =
                        mktac2 () () () "__rename_to"
                          (fun a448  ->
                             fun a449  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a448
                                 a449)
                          (Obj.magic
                             FStar_Reflection_Embeddings.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit
                         in
                      let uu____2202 =
                        let uu____2205 =
                          mktac1 () () "__binder_retype"
                            (fun a450  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a450)
                            (Obj.magic
                               FStar_Reflection_Embeddings.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2206 =
                          let uu____2209 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2210 =
                            let uu____2213 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2214 =
                              let uu____2217 =
                                mktac1 () () "__clear"
                                  (fun a451  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a451)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit
                                 in
                              let uu____2218 =
                                let uu____2221 =
                                  mktac1 () () "__rewrite"
                                    (fun a452  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a452)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                let uu____2222 =
                                  let uu____2225 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2226 =
                                    let uu____2229 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2230 =
                                      let uu____2233 =
                                        mktac3 () () () () "__t_exact"
                                          (fun a453  ->
                                             fun a454  ->
                                               fun a455  ->
                                                 (Obj.magic
                                                    FStar_Tactics_Basic.t_exact)
                                                   a453 a454 a455)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit
                                         in
                                      let uu____2234 =
                                        let uu____2237 =
                                          mktac1 () () "__apply"
                                            (fun a456  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a456)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____2238 =
                                          let uu____2241 =
                                            mktac1 () () "__apply_raw"
                                              (fun a457  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a457)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____2242 =
                                            let uu____2245 =
                                              mktac1 () () "__apply_lemma"
                                                (fun a458  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a458)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____2246 =
                                              let uu____2249 =
                                                let uu____2250 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a459  ->
                                                     fun a460  ->
                                                       fun a461  ->
                                                         fun a462  ->
                                                           fun a463  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2259
                                                                    ->
                                                                   fun
                                                                    uu____2260
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a459 a460 a461
                                                               a462 a463)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____2250)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2267 =
                                                let uu____2270 =
                                                  mktac1 () ()
                                                    "__set_options"
                                                    (fun a464  ->
                                                       (Obj.magic
                                                          FStar_Tactics_Basic.set_options)
                                                         a464)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.unembed_string)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.embed_unit)
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                let uu____2271 =
                                                  let uu____2274 =
                                                    mktac2 () () () "__seq"
                                                      (fun a465  ->
                                                         fun a466  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.seq)
                                                             a465 a466)
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
                                                  let uu____2275 =
                                                    let uu____2278 =
                                                      mktac1 () () "__tc"
                                                        (fun a467  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a467)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____2279 =
                                                      let uu____2282 =
                                                        mktac1 () ()
                                                          "__unshelve"
                                                          (fun a468  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a468)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____2283 =
                                                        let uu____2286 =
                                                          mktac2 () () ()
                                                            "__unquote"
                                                            (fun a469  ->
                                                               fun a470  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a469 a470)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____2287 =
                                                          let uu____2290 =
                                                            mktac1 () ()
                                                              "__prune"
                                                              (fun a471  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a471)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____2291 =
                                                            let uu____2294 =
                                                              mktac1 () ()
                                                                "__addns"
                                                                (fun a472  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a472)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____2295 =
                                                              let uu____2298
                                                                =
                                                                mktac1 () ()
                                                                  "__print"
                                                                  (fun a473 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun x 
                                                                    ->
                                                                    FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                    FStar_Tactics_Basic.ret
                                                                    ())) a473)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____2303
                                                                =
                                                                let uu____2306
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "__dump"
                                                                    (
                                                                    fun a474 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a474)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____2307
                                                                  =
                                                                  let uu____2310
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__dump1"
                                                                    (fun a475
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a475)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                  let uu____2311
                                                                    =
                                                                    let uu____2314
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a476
                                                                     ->
                                                                    fun a477 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a476 a477)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2315
                                                                    =
                                                                    let uu____2318
                                                                    =
                                                                    let uu____2319
                                                                    =
                                                                    let uu____2330
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_pair
                                                                    FStar_Syntax_Embeddings.unembed_bool
                                                                    FStar_Syntax_Embeddings.unembed_int
                                                                     in
                                                                    unembed_tactic_1
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    uu____2330
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__topdown_rewrite"
                                                                    (fun a478
                                                                     ->
                                                                    fun a479 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.topdown_rewrite)
                                                                    a478 a479)
                                                                    (Obj.magic
                                                                    uu____2319)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2349
                                                                    =
                                                                    let uu____2352
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2353
                                                                    =
                                                                    let uu____2356
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2357
                                                                    =
                                                                    let uu____2360
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2361
                                                                    =
                                                                    let uu____2364
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2365
                                                                    =
                                                                    let uu____2368
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2369
                                                                    =
                                                                    let uu____2372
                                                                    =
                                                                    let uu____2373
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2380
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "__cases"
                                                                    (fun a480
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a480)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2373)
                                                                    uu____2380
                                                                     in
                                                                    let uu____2387
                                                                    =
                                                                    let uu____2390
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2391
                                                                    =
                                                                    let uu____2394
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2395
                                                                    =
                                                                    let uu____2398
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2399
                                                                    =
                                                                    let uu____2402
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2403
                                                                    =
                                                                    let uu____2406
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2407
                                                                    =
                                                                    let uu____2410
                                                                    =
                                                                    let uu____2411
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Embeddings.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__uvar_env"
                                                                    (fun a481
                                                                     ->
                                                                    fun a482 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a481 a482)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2411)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2420
                                                                    =
                                                                    let uu____2423
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__unify"
                                                                    (fun a483
                                                                     ->
                                                                    fun a484 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a483 a484)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2424
                                                                    =
                                                                    let uu____2427
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "__launch_process"
                                                                    (fun a485
                                                                     ->
                                                                    fun a486 
                                                                    ->
                                                                    fun a487 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a485 a486
                                                                    a487)
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
                                                                    let uu____2428
                                                                    =
                                                                    let uu____2431
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__fresh_bv_named"
                                                                    (fun a488
                                                                     ->
                                                                    fun a489 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_bv_named)
                                                                    a488 a489)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_bv)
                                                                    FStar_Syntax_Syntax.t_bv
                                                                     in
                                                                    [uu____2431;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step]
                                                                     in
                                                                    uu____2427
                                                                    ::
                                                                    uu____2428
                                                                     in
                                                                    uu____2423
                                                                    ::
                                                                    uu____2424
                                                                     in
                                                                    uu____2410
                                                                    ::
                                                                    uu____2420
                                                                     in
                                                                    uu____2406
                                                                    ::
                                                                    uu____2407
                                                                     in
                                                                    uu____2402
                                                                    ::
                                                                    uu____2403
                                                                     in
                                                                    uu____2398
                                                                    ::
                                                                    uu____2399
                                                                     in
                                                                    uu____2394
                                                                    ::
                                                                    uu____2395
                                                                     in
                                                                    uu____2390
                                                                    ::
                                                                    uu____2391
                                                                     in
                                                                    uu____2372
                                                                    ::
                                                                    uu____2387
                                                                     in
                                                                    uu____2368
                                                                    ::
                                                                    uu____2369
                                                                     in
                                                                    uu____2364
                                                                    ::
                                                                    uu____2365
                                                                     in
                                                                    uu____2360
                                                                    ::
                                                                    uu____2361
                                                                     in
                                                                    uu____2356
                                                                    ::
                                                                    uu____2357
                                                                     in
                                                                    uu____2352
                                                                    ::
                                                                    uu____2353
                                                                     in
                                                                    uu____2318
                                                                    ::
                                                                    uu____2349
                                                                     in
                                                                    uu____2314
                                                                    ::
                                                                    uu____2315
                                                                     in
                                                                  uu____2310
                                                                    ::
                                                                    uu____2311
                                                                   in
                                                                uu____2306 ::
                                                                  uu____2307
                                                                 in
                                                              uu____2298 ::
                                                                uu____2303
                                                               in
                                                            uu____2294 ::
                                                              uu____2295
                                                             in
                                                          uu____2290 ::
                                                            uu____2291
                                                           in
                                                        uu____2286 ::
                                                          uu____2287
                                                         in
                                                      uu____2282 ::
                                                        uu____2283
                                                       in
                                                    uu____2278 :: uu____2279
                                                     in
                                                  uu____2274 :: uu____2275
                                                   in
                                                uu____2270 :: uu____2271  in
                                              uu____2249 :: uu____2267  in
                                            uu____2245 :: uu____2246  in
                                          uu____2241 :: uu____2242  in
                                        uu____2237 :: uu____2238  in
                                      uu____2233 :: uu____2234  in
                                    uu____2229 :: uu____2230  in
                                  uu____2225 :: uu____2226  in
                                uu____2221 :: uu____2222  in
                              uu____2217 :: uu____2218  in
                            uu____2213 :: uu____2214  in
                          uu____2209 :: uu____2210  in
                        uu____2205 :: uu____2206  in
                      uu____2201 :: uu____2202  in
                    uu____2188 :: uu____2198  in
                  uu____2175 :: uu____2185  in
                uu____2162 :: uu____2172  in
              uu____2144 :: uu____2159  in
            uu____2140 :: uu____2141  in
          uu____2123 :: uu____2137  in
        uu____2119 :: uu____2120  in
      uu____2113 :: uu____2116  in
    FStar_List.append uu____2110
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)

and unembed_tactic_1 :
  'Aa 'Ab .
    'Aa FStar_Syntax_Embeddings.embedder ->
      'Ab FStar_Syntax_Embeddings.unembedder ->
        FStar_Syntax_Syntax.term ->
          ('Aa -> 'Ab FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option
  =
  fun arg  ->
    fun res  ->
      fun f  ->
        FStar_Pervasives_Native.Some
          (fun x  ->
             let rng = FStar_Range.dummyRange  in
             let x_tm = arg rng x  in
             let app =
               let uu____2461 =
                 let uu____2462 =
                   let uu____2463 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____2463]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____2462  in
               uu____2461 FStar_Pervasives_Native.None rng  in
             unembed_tactic_0 res app)

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
             let uu____2492 =
               let uu____2493 =
                 let uu____2494 =
                   let uu____2495 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2495  in
                 [uu____2494]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2493  in
             uu____2492 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____2502 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____2502
            then
              let uu____2503 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2503
            else ());
           (let result =
              let uu____2506 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2506 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____2510 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2510
             then
               let uu____2511 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2511
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2556 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2556
                   (fun uu____2560  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2583 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2583
                   (fun uu____2587  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2600 =
                   let uu____2605 =
                     let uu____2606 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2606
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2605)  in
                 FStar_Errors.raise_error uu____2600
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2615 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
        uu____2615

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2671  ->
             match uu____2671 with
             | (r,uu____2691,uv,uu____2693,ty,rng) ->
                 let uu____2696 =
                   let uu____2697 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____2698 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2697 uu____2698 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2696, rng)) is
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
        (let uu____2747 = FStar_ST.op_Bang tacdbg  in
         if uu____2747
         then
           let uu____2767 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2767
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____2771 = FStar_ST.op_Bang tacdbg  in
          if uu____2771
          then
            let uu____2791 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2791
          else ());
         (let uu____2793 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____2793 with
          | (uu____2806,uu____2807,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic1
                   in
                let uu____2814 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____2814 with
                | (env1,uu____2828) ->
                    let env2 =
                      let uu___59_2834 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___59_2834.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___59_2834.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___59_2834.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___59_2834.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___59_2834.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___59_2834.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___59_2834.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___59_2834.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___59_2834.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___59_2834.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___59_2834.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___59_2834.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___59_2834.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___59_2834.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___59_2834.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___59_2834.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___59_2834.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___59_2834.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___59_2834.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___59_2834.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___59_2834.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___59_2834.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___59_2834.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___59_2834.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___59_2834.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___59_2834.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___59_2834.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___59_2834.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___59_2834.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.splice =
                          (uu___59_2834.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___59_2834.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___59_2834.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___59_2834.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___59_2834.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___59_2834.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____2835 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ  in
                    (match uu____2835 with
                     | (ps,w) ->
                         ((let uu____2849 = FStar_ST.op_Bang tacdbg  in
                           if uu____2849
                           then
                             let uu____2869 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____2869
                           else ());
                          (let uu____2871 =
                             FStar_Util.record_time
                               (fun uu____2881  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____2871 with
                           | (res,ms) ->
                               ((let uu____2895 = FStar_ST.op_Bang tacdbg  in
                                 if uu____2895
                                 then
                                   let uu____2915 =
                                     FStar_Util.string_of_int ms  in
                                   FStar_Util.print1
                                     "Tactic ran in %s milliseconds\n"
                                     uu____2915
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____2923,ps1) ->
                                     ((let uu____2926 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____2926
                                       then
                                         let uu____2946 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____2946
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____2953 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____2953
                                           then
                                             let uu____2954 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____2954
                                              then ()
                                              else
                                                (let uu____2956 =
                                                   let uu____2957 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____2957
                                                    in
                                                 failwith uu____2956))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___60_2960 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___60_2960.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___60_2960.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___60_2960.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____2962 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env2 g1
                                            in
                                         FStar_All.pipe_right uu____2962
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____2969 =
                                         let uu____2970 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____2970 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____2969 "at the time of failure");
                                      (let uu____2971 =
                                         let uu____2976 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____2976)
                                          in
                                       FStar_Errors.raise_error uu____2971
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2986 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2990 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2994 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3043 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3079 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3129 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3167 . 'Auu____3167 -> 'Auu____3167 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3186 = FStar_Syntax_Util.head_and_args t  in
        match uu____3186 with
        | (hd1,args) ->
            let uu____3223 =
              let uu____3236 =
                let uu____3237 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3237.FStar_Syntax_Syntax.n  in
              (uu____3236, args)  in
            (match uu____3223 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3250))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3313 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3313 with
                       | (gs,uu____3321) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3328 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3328 with
                       | (gs,uu____3336) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3387 =
                        let uu____3394 =
                          let uu____3397 =
                            let uu____3398 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3398
                             in
                          [uu____3397]  in
                        (FStar_Syntax_Util.t_true, uu____3394)  in
                      Simplified uu____3387
                  | Both  ->
                      let uu____3409 =
                        let uu____3422 =
                          let uu____3425 =
                            let uu____3426 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3426
                             in
                          [uu____3425]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3422)  in
                      Dual uu____3409
                  | Neg  -> Simplified (assertion, []))
             | uu____3447 -> Unchanged t)
  
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
    fun uu___57_3527  ->
      match uu___57_3527 with
      | Unchanged t -> let uu____3533 = f t  in Unchanged uu____3533
      | Simplified (t,gs) ->
          let uu____3540 = let uu____3547 = f t  in (uu____3547, gs)  in
          Simplified uu____3540
      | Dual (tn,tp,gs) ->
          let uu____3557 =
            let uu____3566 = f tn  in
            let uu____3567 = f tp  in (uu____3566, uu____3567, gs)  in
          Dual uu____3557
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3621 = f t1 t2  in Unchanged uu____3621
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3633 = let uu____3640 = f t1 t2  in (uu____3640, gs)
               in
            Simplified uu____3633
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3654 = let uu____3661 = f t1 t2  in (uu____3661, gs)
               in
            Simplified uu____3654
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3680 =
              let uu____3687 = f t1 t2  in
              (uu____3687, (FStar_List.append gs1 gs2))  in
            Simplified uu____3680
        | uu____3690 ->
            let uu____3699 = explode x  in
            (match uu____3699 with
             | (n1,p1,gs1) ->
                 let uu____3717 = explode y  in
                 (match uu____3717 with
                  | (n2,p2,gs2) ->
                      let uu____3735 =
                        let uu____3744 = f n1 n2  in
                        let uu____3745 = f p1 p2  in
                        (uu____3744, uu____3745, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3735))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3810 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3810
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3853  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3887 =
              let uu____3888 = FStar_Syntax_Subst.compress t  in
              uu____3888.FStar_Syntax_Syntax.n  in
            match uu____3887 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3900 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3900 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3924 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3924 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3942;
                   FStar_Syntax_Syntax.vars = uu____3943;_},(p,uu____3945)::
                 (q,uu____3947)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3987 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3987
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3990 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3990 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3996 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3996.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4000;
                   FStar_Syntax_Syntax.vars = uu____4001;_},(p,uu____4003)::
                 (q,uu____4005)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4045 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4045
                   in
                let xq =
                  let uu____4047 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4047
                   in
                let r1 =
                  let uu____4049 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4049 p  in
                let r2 =
                  let uu____4051 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4051 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4054,Unchanged uu____4055) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4065 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4065.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4068 ->
                     let uu____4073 = explode r1  in
                     (match uu____4073 with
                      | (pn,pp,gs1) ->
                          let uu____4091 = explode r2  in
                          (match uu____4091 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4112 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4113 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4112
                                   uu____4113
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4165  ->
                       fun r  ->
                         match uu____4165 with
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
                let uu____4283 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4283 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4317  ->
                            match uu____4317 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4331 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___61_4355 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___61_4355.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___61_4355.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4331 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4375 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4375.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4421 = traverse f pol e t1  in
                let uu____4426 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4426 uu____4421
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___62_4464 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___62_4464.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___62_4464.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4471 =
                f pol e
                  (let uu___63_4475 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___63_4475.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___63_4475.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4471
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___64_4485 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___64_4485.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___64_4485.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4486 = explode rp  in
              (match uu____4486 with
               | (uu____4495,p',gs') ->
                   Dual
                     ((let uu___65_4509 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___65_4509.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___65_4509.FStar_Syntax_Syntax.vars)
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
      (let uu____4544 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4544);
      (let uu____4565 = FStar_ST.op_Bang tacdbg  in
       if uu____4565
       then
         let uu____4585 =
           let uu____4586 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4586
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4587 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4585
           uu____4587
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4616 =
         let uu____4623 = traverse by_tactic_interp Pos env goal  in
         match uu____4623 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4641 -> failwith "no"  in
       match uu____4616 with
       | (t',gs) ->
           ((let uu____4663 = FStar_ST.op_Bang tacdbg  in
             if uu____4663
             then
               let uu____4683 =
                 let uu____4684 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4684
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4685 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4683 uu____4685
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4732  ->
                    fun g  ->
                      match uu____4732 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4777 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____4777 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4780 =
                                  let uu____4781 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty
                                     in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4781
                                   in
                                failwith uu____4780
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4784 = FStar_ST.op_Bang tacdbg  in
                            if uu____4784
                            then
                              let uu____4804 = FStar_Util.string_of_int n1
                                 in
                              let uu____4805 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4804 uu____4805
                            else ());
                           (let gt' =
                              let uu____4808 =
                                let uu____4809 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4809
                                 in
                              FStar_TypeChecker_Util.label uu____4808
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____4824 = s1  in
             match uu____4824 with
             | (uu____4845,gs1) ->
                 let uu____4863 =
                   let uu____4870 = FStar_Options.peek ()  in
                   (env, t', uu____4870)  in
                 uu____4863 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4881 =
        let uu____4882 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4882  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4881 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4883 =
      let uu____4884 =
        let uu____4885 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4886 =
          let uu____4889 = FStar_Syntax_Syntax.as_arg a  in [uu____4889]  in
        uu____4885 :: uu____4886  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4884  in
    uu____4883 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4902 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____4902);
        (let uu____4922 =
           let uu____4929 = reify_tactic tau  in
           run_tactic_on_typ uu____4929 env typ  in
         match uu____4922 with
         | (gs,w) ->
             let uu____4936 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4940 =
                      let uu____4941 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4941  in
                    Prims.op_Negation uu____4940) gs
                in
             if uu____4936
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "synthesis left open goals") typ.FStar_Syntax_Syntax.pos
             else w)
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      (let uu____4956 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4956);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____4977 =
         let uu____4984 = reify_tactic tau  in
         run_tactic_on_typ uu____4984 env typ  in
       match uu____4977 with
       | (gs,w) ->
           ((let uu____4994 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4998 =
                      let uu____4999 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4999  in
                    Prims.op_Negation uu____4998) gs
                in
             if uu____4994
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "splice left open goals") typ.FStar_Syntax_Syntax.pos
             else ());
            (let w1 =
               FStar_TypeChecker_Normalize.normalize
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant;
                 FStar_TypeChecker_Normalize.Primops;
                 FStar_TypeChecker_Normalize.Unascribe;
                 FStar_TypeChecker_Normalize.Unmeta] env w
                in
             let uu____5004 =
               let uu____5009 =
                 FStar_Syntax_Embeddings.unembed_list
                   FStar_Reflection_Embeddings.unembed_sigelt
                  in
               uu____5009 w1  in
             FStar_All.pipe_left FStar_Util.must uu____5004)))
  