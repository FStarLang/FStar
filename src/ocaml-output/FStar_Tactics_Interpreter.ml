open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
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
                | (embedded_state,uu____68)::[] ->
                    let uu____85 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state
                       in
                    FStar_Util.bind_opt uu____85
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____98  ->
                              let uu____99 = FStar_Ident.string_of_lid nm  in
                              let uu____100 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.print2 "Reached %s, args are: %s\n"
                                uu____99 uu____100);
                         (let res =
                            let uu____102 =
                              FStar_TypeChecker_Normalize.psc_range psc  in
                            let uu____103 = FStar_Tactics_Basic.run t ps1  in
                            let uu____106 =
                              FStar_Tactics_Embedding.embed_result embed_r
                                t_r
                               in
                            uu____106 uu____102 uu____103  in
                          FStar_Pervasives_Native.Some res))
                | uu____120 ->
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
                  | (a,uu____197)::(embedded_state,uu____199)::[] ->
                      let uu____226 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____226
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____239  ->
                                let uu____240 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____241 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____240
                                  uu____241);
                           (let uu____242 = unembed_a a  in
                            FStar_Util.bind_opt uu____242
                              (fun a1  ->
                                 let res =
                                   let uu____254 = t a1  in
                                   FStar_Tactics_Basic.run uu____254 ps1  in
                                 let uu____257 =
                                   let uu____258 =
                                     FStar_TypeChecker_Normalize.psc_range
                                       psc
                                      in
                                   let uu____259 =
                                     FStar_Tactics_Embedding.embed_result
                                       embed_r t_r
                                      in
                                   uu____259 uu____258 res  in
                                 FStar_Pervasives_Native.Some uu____257)))
                  | uu____273 ->
                      let uu____274 =
                        let uu____275 = FStar_Ident.string_of_lid nm  in
                        let uu____276 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____275 uu____276
                         in
                      failwith uu____274
  
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
                  | (a,uu____358)::(embedded_state,uu____360)::[] ->
                      let uu____387 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____387
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____400  ->
                                let uu____401 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____402 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____401
                                  uu____402);
                           (let uu____403 = unembed_a a  in
                            FStar_Util.bind_opt uu____403
                              (fun a1  ->
                                 let res =
                                   let uu____415 = t psc a1  in
                                   FStar_Tactics_Basic.run uu____415 ps1  in
                                 let uu____418 =
                                   let uu____419 =
                                     FStar_TypeChecker_Normalize.psc_range
                                       psc
                                      in
                                   let uu____420 =
                                     FStar_Tactics_Embedding.embed_result
                                       embed_r t_r
                                      in
                                   uu____420 uu____419 res  in
                                 FStar_Pervasives_Native.Some uu____418)))
                  | uu____434 ->
                      let uu____435 =
                        let uu____436 = FStar_Ident.string_of_lid nm  in
                        let uu____437 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____436 uu____437
                         in
                      failwith uu____435
  
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
                    | (a,uu____534)::(b,uu____536)::(embedded_state,uu____538)::[]
                        ->
                        let uu____575 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____575
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____588  ->
                                  let uu____589 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____590 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____589
                                    uu____590);
                             (let uu____591 = unembed_a a  in
                              FStar_Util.bind_opt uu____591
                                (fun a1  ->
                                   let uu____599 = unembed_b b  in
                                   FStar_Util.bind_opt uu____599
                                     (fun b1  ->
                                        let res =
                                          let uu____611 = t a1 b1  in
                                          FStar_Tactics_Basic.run uu____611
                                            ps1
                                           in
                                        let uu____614 =
                                          let uu____615 =
                                            FStar_TypeChecker_Normalize.psc_range
                                              psc
                                             in
                                          let uu____616 =
                                            FStar_Tactics_Embedding.embed_result
                                              embed_r t_r
                                             in
                                          uu____616 uu____615 res  in
                                        FStar_Pervasives_Native.Some
                                          uu____614))))
                    | uu____630 ->
                        let uu____631 =
                          let uu____632 = FStar_Ident.string_of_lid nm  in
                          let uu____633 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____632 uu____633
                           in
                        failwith uu____631
  
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
                      | (a,uu____750)::(b,uu____752)::(c,uu____754)::
                          (embedded_state,uu____756)::[] ->
                          let uu____803 =
                            FStar_Tactics_Embedding.unembed_proofstate
                              embedded_state
                             in
                          FStar_Util.bind_opt uu____803
                            (fun ps  ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____816  ->
                                    let uu____817 =
                                      FStar_Ident.string_of_lid nm  in
                                    let uu____818 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state
                                       in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n" uu____817
                                      uu____818);
                               (let uu____819 = unembed_a a  in
                                FStar_Util.bind_opt uu____819
                                  (fun a1  ->
                                     let uu____827 = unembed_b b  in
                                     FStar_Util.bind_opt uu____827
                                       (fun b1  ->
                                          let uu____835 = unembed_c c  in
                                          FStar_Util.bind_opt uu____835
                                            (fun c1  ->
                                               let res =
                                                 let uu____847 = t a1 b1 c1
                                                    in
                                                 FStar_Tactics_Basic.run
                                                   uu____847 ps1
                                                  in
                                               let uu____850 =
                                                 let uu____851 =
                                                   FStar_TypeChecker_Normalize.psc_range
                                                     psc
                                                    in
                                                 let uu____852 =
                                                   FStar_Tactics_Embedding.embed_result
                                                     embed_r t_r
                                                    in
                                                 uu____852 uu____851 res  in
                                               FStar_Pervasives_Native.Some
                                                 uu____850)))))
                      | uu____866 ->
                          let uu____867 =
                            let uu____868 = FStar_Ident.string_of_lid nm  in
                            let uu____869 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____868 uu____869
                             in
                          failwith uu____867
  
let mk_tactic_interpretation_4 :
  'a 'b 'c 'd 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'd -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'c FStar_Syntax_Embeddings.unembedder ->
              'd FStar_Syntax_Embeddings.unembedder ->
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
              fun embed_r  ->
                fun t_r  ->
                  fun nm  ->
                    fun psc  ->
                      fun args  ->
                        match args with
                        | (a,uu____1006)::(b,uu____1008)::(c,uu____1010)::
                            (d,uu____1012)::(embedded_state,uu____1014)::[]
                            ->
                            let uu____1071 =
                              FStar_Tactics_Embedding.unembed_proofstate
                                embedded_state
                               in
                            FStar_Util.bind_opt uu____1071
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1084  ->
                                      let uu____1085 =
                                        FStar_Ident.string_of_lid nm  in
                                      let uu____1086 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state
                                         in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1085 uu____1086);
                                 (let uu____1087 = unembed_a a  in
                                  FStar_Util.bind_opt uu____1087
                                    (fun a1  ->
                                       let uu____1095 = unembed_b b  in
                                       FStar_Util.bind_opt uu____1095
                                         (fun b1  ->
                                            let uu____1103 = unembed_c c  in
                                            FStar_Util.bind_opt uu____1103
                                              (fun c1  ->
                                                 let uu____1111 = unembed_d d
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____1111
                                                   (fun d1  ->
                                                      let res =
                                                        let uu____1123 =
                                                          t a1 b1 c1 d1  in
                                                        FStar_Tactics_Basic.run
                                                          uu____1123 ps1
                                                         in
                                                      let uu____1126 =
                                                        let uu____1127 =
                                                          FStar_TypeChecker_Normalize.psc_range
                                                            psc
                                                           in
                                                        let uu____1128 =
                                                          FStar_Tactics_Embedding.embed_result
                                                            embed_r t_r
                                                           in
                                                        uu____1128 uu____1127
                                                          res
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____1126))))))
                        | uu____1142 ->
                            let uu____1143 =
                              let uu____1144 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____1145 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1144 uu____1145
                               in
                            failwith uu____1143
  
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
                          | (a,uu____1302)::(b,uu____1304)::(c,uu____1306)::
                              (d,uu____1308)::(e,uu____1310)::(embedded_state,uu____1312)::[]
                              ->
                              let uu____1379 =
                                FStar_Tactics_Embedding.unembed_proofstate
                                  embedded_state
                                 in
                              FStar_Util.bind_opt uu____1379
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1392  ->
                                        let uu____1393 =
                                          FStar_Ident.string_of_lid nm  in
                                        let uu____1394 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state
                                           in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1393 uu____1394);
                                   (let uu____1395 = unembed_a a  in
                                    FStar_Util.bind_opt uu____1395
                                      (fun a1  ->
                                         let uu____1403 = unembed_b b  in
                                         FStar_Util.bind_opt uu____1403
                                           (fun b1  ->
                                              let uu____1411 = unembed_c c
                                                 in
                                              FStar_Util.bind_opt uu____1411
                                                (fun c1  ->
                                                   let uu____1419 =
                                                     unembed_d d  in
                                                   FStar_Util.bind_opt
                                                     uu____1419
                                                     (fun d1  ->
                                                        let uu____1427 =
                                                          unembed_e e  in
                                                        FStar_Util.bind_opt
                                                          uu____1427
                                                          (fun e1  ->
                                                             let res =
                                                               let uu____1439
                                                                 =
                                                                 t a1 b1 c1
                                                                   d1 e1
                                                                  in
                                                               FStar_Tactics_Basic.run
                                                                 uu____1439
                                                                 ps1
                                                                in
                                                             let uu____1442 =
                                                               let uu____1443
                                                                 =
                                                                 FStar_TypeChecker_Normalize.psc_range
                                                                   psc
                                                                  in
                                                               let uu____1444
                                                                 =
                                                                 FStar_Tactics_Embedding.embed_result
                                                                   embed_r
                                                                   t_r
                                                                  in
                                                               uu____1444
                                                                 uu____1443
                                                                 res
                                                                in
                                                             FStar_Pervasives_Native.Some
                                                               uu____1442)))))))
                          | uu____1458 ->
                              let uu____1459 =
                                let uu____1460 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____1461 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1460 uu____1461
                                 in
                              failwith uu____1459
  
let (step_from_native_step :
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Normalize.primitive_step)
  =
  fun s  ->
    {
      FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
      FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
      FStar_TypeChecker_Normalize.auto_reflect =
        (FStar_Pervasives_Native.Some
           (s.FStar_Tactics_Native.arity - (Prims.parse_int "1")));
      FStar_TypeChecker_Normalize.strong_reduction_ok =
        (s.FStar_Tactics_Native.strong_reduction_ok);
      FStar_TypeChecker_Normalize.requires_binder_substitution = false;
      FStar_TypeChecker_Normalize.interpretation =
        (fun psc  -> fun args  -> s.FStar_Tactics_Native.tactic psc args)
    }
  
let rec (primitive_steps :
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____1547  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]
         in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
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
      | (ps,uu____2035)::[] ->
          let uu____2052 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2052
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2060 =
                 let uu____2061 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2062 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____2061
                   uu____2062
                  in
               FStar_Pervasives_Native.Some uu____2060)
      | uu____2063 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____2067 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2067;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____2080)::[] ->
          let uu____2097 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2097
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2105 =
                 let uu____2106 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2107 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____2106
                   uu____2107
                  in
               FStar_Pervasives_Native.Some uu____2105)
      | uu____2108 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____2112 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2112;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____2129)::[] ->
          let uu____2146 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2146
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2159 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2176)::(r,uu____2178)::[] ->
          let uu____2205 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2205
            (fun ps1  ->
               let uu____2211 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____2211
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2219 =
                      let uu____2220 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____2220 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2219))
      | uu____2221 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____2236)::(b,uu____2238)::[] ->
          let uu____2265 = FStar_Reflection_Embeddings.unembed_env env_t  in
          FStar_Util.bind_opt uu____2265
            (fun env  ->
               let uu____2271 = FStar_Reflection_Embeddings.unembed_binder b
                  in
               FStar_Util.bind_opt uu____2271
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____2279 =
                      FStar_Reflection_Embeddings.embed_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____2279))
      | uu____2280 -> failwith "Unexpected application of push_binder"  in
    let set_proofstate_range_step =
      let nm =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
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
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      }  in
    let push_binder_step =
      let nm =
        FStar_Tactics_Embedding.fstar_tactics_lid'
          ["Builtins"; "push_binder"]
         in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = push_binder_interp
      }  in
    let put1 rng t =
      let uu___58_2296 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___58_2296.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___58_2296.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____2303 =
      let uu____2306 =
        mktac2 () () () "__fail"
          (fun a438  ->
             fun a439  ->
               (Obj.magic (fun uu____2308  -> FStar_Tactics_Basic.fail)) a438
                 a439) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____2309 =
        let uu____2312 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____2313 =
          let uu____2316 =
            let uu____2317 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a440  ->
                 fun a441  ->
                   (Obj.magic (fun uu____2323  -> FStar_Tactics_Basic.trytac))
                     a440 a441) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____2317)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2330 =
            let uu____2333 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Embeddings.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____2334 =
              let uu____2337 =
                let uu____2338 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____2345 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____2338) uu____2345
                 in
              let uu____2352 =
                let uu____2355 =
                  let uu____2356 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "__norm"
                    (fun a442  -> (Obj.magic FStar_Tactics_Basic.norm) a442)
                    (Obj.magic uu____2356)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____2365 =
                  let uu____2368 =
                    let uu____2369 =
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
                      (Obj.magic uu____2369)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_term)
                      (Obj.magic FStar_Reflection_Embeddings.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2378 =
                    let uu____2381 =
                      let uu____2382 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "__norm_binder_type"
                        (fun a446  ->
                           fun a447  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a446 a447) (Obj.magic uu____2382)
                        (Obj.magic FStar_Reflection_Embeddings.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2391 =
                      let uu____2394 =
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
                      let uu____2395 =
                        let uu____2398 =
                          mktac1 () () "__binder_retype"
                            (fun a450  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a450)
                            (Obj.magic
                               FStar_Reflection_Embeddings.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2399 =
                          let uu____2402 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2403 =
                            let uu____2406 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2407 =
                              let uu____2410 =
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
                              let uu____2411 =
                                let uu____2414 =
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
                                let uu____2415 =
                                  let uu____2418 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2419 =
                                    let uu____2422 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2423 =
                                      let uu____2426 =
                                        mktac2 () () () "__t_exact"
                                          (fun a453  ->
                                             fun a454  ->
                                               (Obj.magic
                                                  FStar_Tactics_Basic.t_exact)
                                                 a453 a454)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit
                                         in
                                      let uu____2427 =
                                        let uu____2430 =
                                          mktac1 () () "__apply"
                                            (fun a455  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a455)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____2431 =
                                          let uu____2434 =
                                            mktac1 () () "__apply_raw"
                                              (fun a456  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a456)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____2435 =
                                            let uu____2438 =
                                              mktac1 () () "__apply_lemma"
                                                (fun a457  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a457)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____2439 =
                                              let uu____2442 =
                                                let uu____2443 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a458  ->
                                                     fun a459  ->
                                                       fun a460  ->
                                                         fun a461  ->
                                                           fun a462  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2452
                                                                    ->
                                                                   fun
                                                                    uu____2453
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a458 a459 a460
                                                               a461 a462)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____2443)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2460 =
                                                let uu____2463 =
                                                  mktac1 () ()
                                                    "__set_options"
                                                    (fun a463  ->
                                                       (Obj.magic
                                                          FStar_Tactics_Basic.set_options)
                                                         a463)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.unembed_string)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.embed_unit)
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                let uu____2464 =
                                                  let uu____2467 =
                                                    mktac2 () () () "__seq"
                                                      (fun a464  ->
                                                         fun a465  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.seq)
                                                             a464 a465)
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
                                                  let uu____2468 =
                                                    let uu____2471 =
                                                      mktac1 () () "__tc"
                                                        (fun a466  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a466)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____2472 =
                                                      let uu____2475 =
                                                        mktac1 () ()
                                                          "__unshelve"
                                                          (fun a467  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a467)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____2476 =
                                                        let uu____2479 =
                                                          mktac2 () () ()
                                                            "__unquote"
                                                            (fun a468  ->
                                                               fun a469  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a468 a469)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____2480 =
                                                          let uu____2483 =
                                                            mktac1 () ()
                                                              "__prune"
                                                              (fun a470  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a470)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____2484 =
                                                            let uu____2487 =
                                                              mktac1 () ()
                                                                "__addns"
                                                                (fun a471  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a471)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____2488 =
                                                              let uu____2491
                                                                =
                                                                mktac1 () ()
                                                                  "__print"
                                                                  (fun a472 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun x 
                                                                    ->
                                                                    FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                    FStar_Tactics_Basic.ret
                                                                    ())) a472)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____2496
                                                                =
                                                                let uu____2499
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "__dump"
                                                                    (
                                                                    fun a473 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a473)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____2500
                                                                  =
                                                                  let uu____2503
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__dump1"
                                                                    (fun a474
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a474)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                  let uu____2504
                                                                    =
                                                                    let uu____2507
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a475
                                                                     ->
                                                                    fun a476 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a475 a476)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2508
                                                                    =
                                                                    let uu____2511
                                                                    =
                                                                    let uu____2512
                                                                    =
                                                                    let uu____2523
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_pair
                                                                    FStar_Syntax_Embeddings.unembed_bool
                                                                    FStar_Syntax_Embeddings.unembed_int
                                                                     in
                                                                    unembed_tactic_1
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    uu____2523
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__topdown_rewrite"
                                                                    (fun a477
                                                                     ->
                                                                    fun a478 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.topdown_rewrite)
                                                                    a477 a478)
                                                                    (Obj.magic
                                                                    uu____2512)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2542
                                                                    =
                                                                    let uu____2545
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2546
                                                                    =
                                                                    let uu____2549
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2550
                                                                    =
                                                                    let uu____2553
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2554
                                                                    =
                                                                    let uu____2557
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2558
                                                                    =
                                                                    let uu____2561
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2562
                                                                    =
                                                                    let uu____2565
                                                                    =
                                                                    mktac0 ()
                                                                    "__dismiss"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dismiss)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2566
                                                                    =
                                                                    let uu____2569
                                                                    =
                                                                    mktac0 ()
                                                                    "__tadmit"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.tadmit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2570
                                                                    =
                                                                    let uu____2573
                                                                    =
                                                                    let uu____2574
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2581
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "__cases"
                                                                    (fun a479
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a479)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2574)
                                                                    uu____2581
                                                                     in
                                                                    let uu____2588
                                                                    =
                                                                    let uu____2591
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2592
                                                                    =
                                                                    let uu____2595
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2596
                                                                    =
                                                                    let uu____2599
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2600
                                                                    =
                                                                    let uu____2603
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2604
                                                                    =
                                                                    let uu____2607
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__inspect"
                                                                    (fun a480
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.inspect)
                                                                    a480)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term_view)
                                                                    FStar_Reflection_Data.fstar_refl_term_view
                                                                     in
                                                                    let uu____2608
                                                                    =
                                                                    let uu____2611
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__pack"
                                                                    (fun a481
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pack)
                                                                    a481)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term_view)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2612
                                                                    =
                                                                    let uu____2615
                                                                    =
                                                                    mktac0 ()
                                                                    "__ngoals"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2616
                                                                    =
                                                                    let uu____2619
                                                                    =
                                                                    mktac0 ()
                                                                    "__ngoals_smt"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals_smt)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2620
                                                                    =
                                                                    let uu____2623
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2624
                                                                    =
                                                                    let uu____2627
                                                                    =
                                                                    let uu____2628
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Embeddings.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__uvar_env"
                                                                    (fun a482
                                                                     ->
                                                                    fun a483 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a482 a483)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2628)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2637
                                                                    =
                                                                    let uu____2640
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__unify"
                                                                    (fun a484
                                                                     ->
                                                                    fun a485 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a484 a485)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2641
                                                                    =
                                                                    let uu____2644
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "__launch_process"
                                                                    (fun a486
                                                                     ->
                                                                    fun a487 
                                                                    ->
                                                                    fun a488 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a486 a487
                                                                    a488)
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
                                                                    let uu____2645
                                                                    =
                                                                    let uu____2648
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__fresh_bv_named"
                                                                    (fun a489
                                                                     ->
                                                                    fun a490 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_bv_named)
                                                                    a489 a490)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_bv)
                                                                    FStar_Syntax_Syntax.t_bv
                                                                     in
                                                                    let uu____2649
                                                                    =
                                                                    let uu____2652
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__change"
                                                                    (fun a491
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.change)
                                                                    a491)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2653
                                                                    =
                                                                    let uu____2656
                                                                    =
                                                                    mktac0 ()
                                                                    "__get_guard_policy"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.get_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.embed_guard_policy)
                                                                    FStar_Tactics_Embedding.t_guard_policy
                                                                     in
                                                                    let uu____2657
                                                                    =
                                                                    let uu____2660
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__set_guard_policy"
                                                                    (fun a492
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.set_guard_policy)
                                                                    a492)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    [uu____2660;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____2656
                                                                    ::
                                                                    uu____2657
                                                                     in
                                                                    uu____2652
                                                                    ::
                                                                    uu____2653
                                                                     in
                                                                    uu____2648
                                                                    ::
                                                                    uu____2649
                                                                     in
                                                                    uu____2644
                                                                    ::
                                                                    uu____2645
                                                                     in
                                                                    uu____2640
                                                                    ::
                                                                    uu____2641
                                                                     in
                                                                    uu____2627
                                                                    ::
                                                                    uu____2637
                                                                     in
                                                                    uu____2623
                                                                    ::
                                                                    uu____2624
                                                                     in
                                                                    uu____2619
                                                                    ::
                                                                    uu____2620
                                                                     in
                                                                    uu____2615
                                                                    ::
                                                                    uu____2616
                                                                     in
                                                                    uu____2611
                                                                    ::
                                                                    uu____2612
                                                                     in
                                                                    uu____2607
                                                                    ::
                                                                    uu____2608
                                                                     in
                                                                    uu____2603
                                                                    ::
                                                                    uu____2604
                                                                     in
                                                                    uu____2599
                                                                    ::
                                                                    uu____2600
                                                                     in
                                                                    uu____2595
                                                                    ::
                                                                    uu____2596
                                                                     in
                                                                    uu____2591
                                                                    ::
                                                                    uu____2592
                                                                     in
                                                                    uu____2573
                                                                    ::
                                                                    uu____2588
                                                                     in
                                                                    uu____2569
                                                                    ::
                                                                    uu____2570
                                                                     in
                                                                    uu____2565
                                                                    ::
                                                                    uu____2566
                                                                     in
                                                                    uu____2561
                                                                    ::
                                                                    uu____2562
                                                                     in
                                                                    uu____2557
                                                                    ::
                                                                    uu____2558
                                                                     in
                                                                    uu____2553
                                                                    ::
                                                                    uu____2554
                                                                     in
                                                                    uu____2549
                                                                    ::
                                                                    uu____2550
                                                                     in
                                                                    uu____2545
                                                                    ::
                                                                    uu____2546
                                                                     in
                                                                    uu____2511
                                                                    ::
                                                                    uu____2542
                                                                     in
                                                                    uu____2507
                                                                    ::
                                                                    uu____2508
                                                                     in
                                                                  uu____2503
                                                                    ::
                                                                    uu____2504
                                                                   in
                                                                uu____2499 ::
                                                                  uu____2500
                                                                 in
                                                              uu____2491 ::
                                                                uu____2496
                                                               in
                                                            uu____2487 ::
                                                              uu____2488
                                                             in
                                                          uu____2483 ::
                                                            uu____2484
                                                           in
                                                        uu____2479 ::
                                                          uu____2480
                                                         in
                                                      uu____2475 ::
                                                        uu____2476
                                                       in
                                                    uu____2471 :: uu____2472
                                                     in
                                                  uu____2467 :: uu____2468
                                                   in
                                                uu____2463 :: uu____2464  in
                                              uu____2442 :: uu____2460  in
                                            uu____2438 :: uu____2439  in
                                          uu____2434 :: uu____2435  in
                                        uu____2430 :: uu____2431  in
                                      uu____2426 :: uu____2427  in
                                    uu____2422 :: uu____2423  in
                                  uu____2418 :: uu____2419  in
                                uu____2414 :: uu____2415  in
                              uu____2410 :: uu____2411  in
                            uu____2406 :: uu____2407  in
                          uu____2402 :: uu____2403  in
                        uu____2398 :: uu____2399  in
                      uu____2394 :: uu____2395  in
                    uu____2381 :: uu____2391  in
                  uu____2368 :: uu____2378  in
                uu____2355 :: uu____2365  in
              uu____2337 :: uu____2352  in
            uu____2333 :: uu____2334  in
          uu____2316 :: uu____2330  in
        uu____2312 :: uu____2313  in
      uu____2306 :: uu____2309  in
    FStar_List.append uu____2303
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
               let uu____2690 =
                 let uu____2691 =
                   let uu____2692 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____2692]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____2691  in
               uu____2690 FStar_Pervasives_Native.None rng  in
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
             let uu____2721 =
               let uu____2722 =
                 let uu____2723 =
                   let uu____2724 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2724  in
                 [uu____2723]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2722  in
             uu____2721 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____2731 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____2731
            then
              let uu____2732 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2732
            else ());
           (let result =
              let uu____2735 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2735 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____2739 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2739
             then
               let uu____2740 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2740
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2785 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2785
                   (fun uu____2789  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2812 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2812
                   (fun uu____2816  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2829 =
                   let uu____2834 =
                     let uu____2835 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2835
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2834)  in
                 FStar_Errors.raise_error uu____2829
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2844 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
        uu____2844

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2900  ->
             match uu____2900 with
             | (r,uu____2920,uv,uu____2922,ty,rng) ->
                 let uu____2925 =
                   let uu____2926 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____2927 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2926 uu____2927 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2925, rng)) is
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
        (let uu____2976 = FStar_ST.op_Bang tacdbg  in
         if uu____2976
         then
           let uu____2996 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2996
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____3000 = FStar_ST.op_Bang tacdbg  in
          if uu____3000
          then
            let uu____3020 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____3020
          else ());
         (let uu____3022 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____3022 with
          | (uu____3035,uu____3036,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic1
                   in
                let uu____3043 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____3043 with
                | (env1,uu____3057) ->
                    let env2 =
                      let uu___59_3063 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___59_3063.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___59_3063.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___59_3063.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___59_3063.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___59_3063.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___59_3063.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___59_3063.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___59_3063.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___59_3063.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___59_3063.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___59_3063.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___59_3063.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___59_3063.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___59_3063.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___59_3063.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___59_3063.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___59_3063.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___59_3063.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___59_3063.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___59_3063.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___59_3063.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___59_3063.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___59_3063.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___59_3063.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___59_3063.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___59_3063.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___59_3063.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___59_3063.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___59_3063.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.splice =
                          (uu___59_3063.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___59_3063.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___59_3063.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___59_3063.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___59_3063.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___59_3063.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let env3 =
                      let uu___60_3065 = env2  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___60_3065.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___60_3065.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___60_3065.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___60_3065.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___60_3065.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___60_3065.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___60_3065.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___60_3065.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___60_3065.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___60_3065.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___60_3065.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___60_3065.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___60_3065.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___60_3065.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___60_3065.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___60_3065.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___60_3065.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___60_3065.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___60_3065.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes = true;
                        FStar_TypeChecker_Env.failhard =
                          (uu___60_3065.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___60_3065.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___60_3065.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___60_3065.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___60_3065.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___60_3065.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___60_3065.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___60_3065.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___60_3065.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___60_3065.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.splice =
                          (uu___60_3065.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___60_3065.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___60_3065.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___60_3065.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___60_3065.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___60_3065.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____3066 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ  in
                    (match uu____3066 with
                     | (ps,w) ->
                         ((let uu____3080 = FStar_ST.op_Bang tacdbg  in
                           if uu____3080
                           then
                             let uu____3100 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____3100
                           else ());
                          (let uu____3102 =
                             FStar_Util.record_time
                               (fun uu____3112  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____3102 with
                           | (res,ms) ->
                               ((let uu____3126 = FStar_ST.op_Bang tacdbg  in
                                 if uu____3126
                                 then
                                   let uu____3146 =
                                     FStar_Syntax_Print.term_to_string
                                       tactic1
                                      in
                                   let uu____3147 =
                                     FStar_Util.string_of_int ms  in
                                   let uu____3148 =
                                     FStar_Syntax_Print.lid_to_string
                                       env3.FStar_TypeChecker_Env.curmodule
                                      in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____3146 uu____3147 uu____3148
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____3156,ps1) ->
                                     ((let uu____3159 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____3159
                                       then
                                         let uu____3179 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____3179
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____3186 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____3186
                                           then
                                             let uu____3187 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____3187
                                              then ()
                                              else
                                                (let uu____3189 =
                                                   let uu____3190 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____3190
                                                    in
                                                 failwith uu____3189))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___61_3193 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___61_3193.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___61_3193.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___61_3193.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____3195 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env3 g1
                                            in
                                         FStar_All.pipe_right uu____3195
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____3202 =
                                         let uu____3203 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____3203 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____3202 "at the time of failure");
                                      (let uu____3204 =
                                         let uu____3209 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____3209)
                                          in
                                       FStar_Errors.raise_error uu____3204
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____3219 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____3223 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____3227 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3276 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3312 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3362 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3400 . 'Auu____3400 -> 'Auu____3400 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3419 = FStar_Syntax_Util.head_and_args t  in
        match uu____3419 with
        | (hd1,args) ->
            let uu____3456 =
              let uu____3469 =
                let uu____3470 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3470.FStar_Syntax_Syntax.n  in
              (uu____3469, args)  in
            (match uu____3456 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3483))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3546 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3546 with
                       | (gs,uu____3554) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3561 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3561 with
                       | (gs,uu____3569) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3620 =
                        let uu____3627 =
                          let uu____3630 =
                            let uu____3631 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3631
                             in
                          [uu____3630]  in
                        (FStar_Syntax_Util.t_true, uu____3627)  in
                      Simplified uu____3620
                  | Both  ->
                      let uu____3642 =
                        let uu____3655 =
                          let uu____3658 =
                            let uu____3659 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3659
                             in
                          [uu____3658]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3655)  in
                      Dual uu____3642
                  | Neg  -> Simplified (assertion, []))
             | uu____3680 -> Unchanged t)
  
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
    fun uu___57_3760  ->
      match uu___57_3760 with
      | Unchanged t -> let uu____3766 = f t  in Unchanged uu____3766
      | Simplified (t,gs) ->
          let uu____3773 = let uu____3780 = f t  in (uu____3780, gs)  in
          Simplified uu____3773
      | Dual (tn,tp,gs) ->
          let uu____3790 =
            let uu____3799 = f tn  in
            let uu____3800 = f tp  in (uu____3799, uu____3800, gs)  in
          Dual uu____3790
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3854 = f t1 t2  in Unchanged uu____3854
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3866 = let uu____3873 = f t1 t2  in (uu____3873, gs)
               in
            Simplified uu____3866
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3887 = let uu____3894 = f t1 t2  in (uu____3894, gs)
               in
            Simplified uu____3887
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3913 =
              let uu____3920 = f t1 t2  in
              (uu____3920, (FStar_List.append gs1 gs2))  in
            Simplified uu____3913
        | uu____3923 ->
            let uu____3932 = explode x  in
            (match uu____3932 with
             | (n1,p1,gs1) ->
                 let uu____3950 = explode y  in
                 (match uu____3950 with
                  | (n2,p2,gs2) ->
                      let uu____3968 =
                        let uu____3977 = f n1 n2  in
                        let uu____3978 = f p1 p2  in
                        (uu____3977, uu____3978, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3968))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____4043 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____4043
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____4086  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____4120 =
              let uu____4121 = FStar_Syntax_Subst.compress t  in
              uu____4121.FStar_Syntax_Syntax.n  in
            match uu____4120 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____4133 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____4133 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____4157 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____4157 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4175;
                   FStar_Syntax_Syntax.vars = uu____4176;_},(p,uu____4178)::
                 (q,uu____4180)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____4220 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4220
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____4223 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____4223 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4229 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4229.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4233;
                   FStar_Syntax_Syntax.vars = uu____4234;_},(p,uu____4236)::
                 (q,uu____4238)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4278 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4278
                   in
                let xq =
                  let uu____4280 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4280
                   in
                let r1 =
                  let uu____4282 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4282 p  in
                let r2 =
                  let uu____4284 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4284 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4287,Unchanged uu____4288) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4298 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4298.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4301 ->
                     let uu____4306 = explode r1  in
                     (match uu____4306 with
                      | (pn,pp,gs1) ->
                          let uu____4324 = explode r2  in
                          (match uu____4324 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4345 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4346 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4345
                                   uu____4346
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4398  ->
                       fun r  ->
                         match uu____4398 with
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
                let uu____4516 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4516 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4550  ->
                            match uu____4550 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4564 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___62_4588 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___62_4588.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___62_4588.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4564 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4608 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4608.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4654 = traverse f pol e t1  in
                let uu____4659 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4659 uu____4654
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___63_4697 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___63_4697.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___63_4697.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4704 =
                f pol e
                  (let uu___64_4708 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___64_4708.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___64_4708.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4704
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___65_4718 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___65_4718.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___65_4718.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4719 = explode rp  in
              (match uu____4719 with
               | (uu____4728,p',gs') ->
                   Dual
                     ((let uu___66_4742 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___66_4742.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___66_4742.FStar_Syntax_Syntax.vars)
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
      (let uu____4777 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4777);
      (let uu____4798 = FStar_ST.op_Bang tacdbg  in
       if uu____4798
       then
         let uu____4818 =
           let uu____4819 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4819
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4820 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4818
           uu____4820
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4849 =
         let uu____4856 = traverse by_tactic_interp Pos env goal  in
         match uu____4856 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4874 -> failwith "no"  in
       match uu____4849 with
       | (t',gs) ->
           ((let uu____4896 = FStar_ST.op_Bang tacdbg  in
             if uu____4896
             then
               let uu____4916 =
                 let uu____4917 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4917
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4918 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4916 uu____4918
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4965  ->
                    fun g  ->
                      match uu____4965 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5010 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____5010 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5013 =
                                  let uu____5018 =
                                    let uu____5019 =
                                      FStar_Syntax_Print.term_to_string
                                        g.FStar_Tactics_Types.goal_ty
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5019
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5018)
                                   in
                                FStar_Errors.raise_error uu____5013
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5022 = FStar_ST.op_Bang tacdbg  in
                            if uu____5022
                            then
                              let uu____5042 = FStar_Util.string_of_int n1
                                 in
                              let uu____5043 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5042 uu____5043
                            else ());
                           (let gt' =
                              let uu____5046 =
                                let uu____5047 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____5047
                                 in
                              FStar_TypeChecker_Util.label uu____5046
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____5062 = s1  in
             match uu____5062 with
             | (uu____5083,gs1) ->
                 let uu____5101 =
                   let uu____5108 = FStar_Options.peek ()  in
                   (env, t', uu____5108)  in
                 uu____5101 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____5119 =
        let uu____5120 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____5120  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____5119 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____5121 =
      let uu____5122 =
        let uu____5123 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____5124 =
          let uu____5127 = FStar_Syntax_Syntax.as_arg a  in [uu____5127]  in
        uu____5123 :: uu____5124  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____5122  in
    uu____5121 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____5140 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____5140);
        (let uu____5160 =
           let uu____5167 = reify_tactic tau  in
           run_tactic_on_typ uu____5167 env typ  in
         match uu____5160 with
         | (gs,w) ->
             let uu____5174 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5178 =
                      let uu____5179 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5179  in
                    Prims.op_Negation uu____5178) gs
                in
             if uu____5174
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
      (let uu____5194 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5194);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____5215 =
         let uu____5222 = reify_tactic tau  in
         run_tactic_on_typ uu____5222 env typ  in
       match uu____5215 with
       | (gs,w) ->
           ((let uu____5232 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5236 =
                      let uu____5237 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5237  in
                    Prims.op_Negation uu____5236) gs
                in
             if uu____5232
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
             let uu____5242 =
               let uu____5247 =
                 FStar_Syntax_Embeddings.unembed_list
                   FStar_Reflection_Embeddings.unembed_sigelt
                  in
               uu____5247 w1  in
             FStar_All.pipe_left FStar_Util.must uu____5242)))
  