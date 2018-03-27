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
  
let mk_tactic_interpretation_6 :
  'a 'b 'c 'd 'e 'f 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'c FStar_Syntax_Embeddings.unembedder ->
              'd FStar_Syntax_Embeddings.unembedder ->
                'e FStar_Syntax_Embeddings.unembedder ->
                  'f FStar_Syntax_Embeddings.unembedder ->
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
                fun unembed_f  ->
                  fun embed_r  ->
                    fun t_r  ->
                      fun nm  ->
                        fun psc  ->
                          fun args  ->
                            match args with
                            | (a,uu____1638)::(b,uu____1640)::(c,uu____1642)::
                                (d,uu____1644)::(e,uu____1646)::(f,uu____1648)::
                                (embedded_state,uu____1650)::[] ->
                                let uu____1727 =
                                  FStar_Tactics_Embedding.unembed_proofstate
                                    embedded_state
                                   in
                                FStar_Util.bind_opt uu____1727
                                  (fun ps  ->
                                     let ps1 =
                                       FStar_Tactics_Types.set_ps_psc psc ps
                                        in
                                     FStar_Tactics_Basic.log ps1
                                       (fun uu____1740  ->
                                          let uu____1741 =
                                            FStar_Ident.string_of_lid nm  in
                                          let uu____1742 =
                                            FStar_Syntax_Print.term_to_string
                                              embedded_state
                                             in
                                          FStar_Util.print2
                                            "Reached %s, goals are: %s\n"
                                            uu____1741 uu____1742);
                                     (let uu____1743 = unembed_a a  in
                                      FStar_Util.bind_opt uu____1743
                                        (fun a1  ->
                                           let uu____1751 = unembed_b b  in
                                           FStar_Util.bind_opt uu____1751
                                             (fun b1  ->
                                                let uu____1759 = unembed_c c
                                                   in
                                                FStar_Util.bind_opt
                                                  uu____1759
                                                  (fun c1  ->
                                                     let uu____1767 =
                                                       unembed_d d  in
                                                     FStar_Util.bind_opt
                                                       uu____1767
                                                       (fun d1  ->
                                                          let uu____1775 =
                                                            unembed_e e  in
                                                          FStar_Util.bind_opt
                                                            uu____1775
                                                            (fun e1  ->
                                                               let uu____1783
                                                                 =
                                                                 unembed_f f
                                                                  in
                                                               FStar_Util.bind_opt
                                                                 uu____1783
                                                                 (fun f1  ->
                                                                    let res =
                                                                    let uu____1795
                                                                    =
                                                                    t a1 b1
                                                                    c1 d1 e1
                                                                    f1  in
                                                                    FStar_Tactics_Basic.run
                                                                    uu____1795
                                                                    ps1  in
                                                                    let uu____1798
                                                                    =
                                                                    let uu____1799
                                                                    =
                                                                    FStar_TypeChecker_Normalize.psc_range
                                                                    psc  in
                                                                    let uu____1800
                                                                    =
                                                                    FStar_Tactics_Embedding.embed_result
                                                                    embed_r
                                                                    t_r  in
                                                                    uu____1800
                                                                    uu____1799
                                                                    res  in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____1798))))))))
                            | uu____1814 ->
                                let uu____1815 =
                                  let uu____1816 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____1817 =
                                    FStar_Syntax_Print.args_to_string args
                                     in
                                  FStar_Util.format2
                                    "Unexpected application of tactic primitive %s %s"
                                    uu____1816 uu____1817
                                   in
                                failwith uu____1815
  
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
  fun uu____1903  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]
         in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.auto_reflect =
          (FStar_Pervasives_Native.Some (arity - (Prims.parse_int "1")));
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation =
          (fun psc  -> fun args  -> interpretation nm1 psc args)
      }  in
    let native_tactics = FStar_Tactics_Native.list_all ()  in
    let native_tactics_steps =
      FStar_List.map step_from_native_step native_tactics  in
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
      | (ps,uu____2355)::[] ->
          let uu____2372 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2372
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2380 =
                 let uu____2381 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2382 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____2381
                   uu____2382
                  in
               FStar_Pervasives_Native.Some uu____2380)
      | uu____2383 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____2387 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2387;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____2400)::[] ->
          let uu____2417 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2417
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2425 =
                 let uu____2426 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2427 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____2426
                   uu____2427
                  in
               FStar_Pervasives_Native.Some uu____2425)
      | uu____2428 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____2432 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2432;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____2449)::[] ->
          let uu____2466 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2466
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2479 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2496)::(r,uu____2498)::[] ->
          let uu____2525 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2525
            (fun ps1  ->
               let uu____2531 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____2531
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2539 =
                      let uu____2540 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____2540 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2539))
      | uu____2541 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____2556)::(b,uu____2558)::[] ->
          let uu____2585 = FStar_Reflection_Embeddings.unembed_env env_t  in
          FStar_Util.bind_opt uu____2585
            (fun env  ->
               let uu____2591 = FStar_Reflection_Embeddings.unembed_binder b
                  in
               FStar_Util.bind_opt uu____2591
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____2599 =
                      FStar_Reflection_Embeddings.embed_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____2599))
      | uu____2600 -> failwith "Unexpected application of push_binder"  in
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
      let uu___60_2616 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___60_2616.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___60_2616.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____2623 =
      let uu____2626 =
        mktac2 () () () "fail"
          (fun a445  ->
             fun a446  ->
               (Obj.magic (fun uu____2628  -> FStar_Tactics_Basic.fail)) a445
                 a446) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____2629 =
        let uu____2632 =
          mktac1 () () "trivial"
            (fun a447  -> (Obj.magic FStar_Tactics_Basic.trivial) a447)
            (Obj.magic FStar_Syntax_Embeddings.unembed_unit)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____2633 =
          let uu____2636 =
            let uu____2637 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a448  ->
                 fun a449  ->
                   (Obj.magic (fun uu____2643  -> FStar_Tactics_Basic.trytac))
                     a448 a449) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____2637)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2650 =
            let uu____2653 =
              mktac1 () () "intro"
                (fun a450  -> (Obj.magic FStar_Tactics_Basic.intro) a450)
                (Obj.magic FStar_Syntax_Embeddings.unembed_unit)
                (Obj.magic FStar_Reflection_Embeddings.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____2654 =
              let uu____2657 =
                let uu____2658 =
                  FStar_Syntax_Embeddings.embed_tuple2
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____2665 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac1 () () "intro_rec"
                  (fun a451  ->
                     (Obj.magic FStar_Tactics_Basic.intro_rec) a451)
                  (Obj.magic FStar_Syntax_Embeddings.unembed_unit)
                  (Obj.magic uu____2658) uu____2665
                 in
              let uu____2672 =
                let uu____2675 =
                  let uu____2676 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "norm"
                    (fun a452  -> (Obj.magic FStar_Tactics_Basic.norm) a452)
                    (Obj.magic uu____2676)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____2685 =
                  let uu____2688 =
                    let uu____2689 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step
                       in
                    mktac3 () () () () "norm_term_env"
                      (fun a453  ->
                         fun a454  ->
                           fun a455  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a453 a454 a455)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_env)
                      (Obj.magic uu____2689)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_term)
                      (Obj.magic FStar_Reflection_Embeddings.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2698 =
                    let uu____2701 =
                      let uu____2702 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "norm_binder_type"
                        (fun a456  ->
                           fun a457  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a456 a457) (Obj.magic uu____2702)
                        (Obj.magic FStar_Reflection_Embeddings.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2711 =
                      let uu____2714 =
                        mktac2 () () () "rename_to"
                          (fun a458  ->
                             fun a459  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a458
                                 a459)
                          (Obj.magic
                             FStar_Reflection_Embeddings.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit
                         in
                      let uu____2715 =
                        let uu____2718 =
                          mktac1 () () "binder_retype"
                            (fun a460  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a460)
                            (Obj.magic
                               FStar_Reflection_Embeddings.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2719 =
                          let uu____2722 =
                            mktac1 () () "revert"
                              (fun a461  ->
                                 (Obj.magic FStar_Tactics_Basic.revert) a461)
                              (Obj.magic FStar_Syntax_Embeddings.unembed_unit)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2723 =
                            let uu____2726 =
                              mktac1 () () "clear_top"
                                (fun a462  ->
                                   (Obj.magic FStar_Tactics_Basic.clear_top)
                                     a462)
                                (Obj.magic
                                   FStar_Syntax_Embeddings.unembed_unit)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2727 =
                              let uu____2730 =
                                mktac1 () () "clear"
                                  (fun a463  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a463)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit
                                 in
                              let uu____2731 =
                                let uu____2734 =
                                  mktac1 () () "rewrite"
                                    (fun a464  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a464)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                let uu____2735 =
                                  let uu____2738 =
                                    mktac1 () () "smt"
                                      (fun a465  ->
                                         (Obj.magic FStar_Tactics_Basic.smt)
                                           a465)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.unembed_unit)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2739 =
                                    let uu____2742 =
                                      mktac1 () () "refine_intro"
                                        (fun a466  ->
                                           (Obj.magic
                                              FStar_Tactics_Basic.refine_intro)
                                             a466)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.unembed_unit)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2743 =
                                      let uu____2746 =
                                        mktac2 () () () "t_exact"
                                          (fun a467  ->
                                             fun a468  ->
                                               (Obj.magic
                                                  FStar_Tactics_Basic.t_exact)
                                                 a467 a468)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit
                                         in
                                      let uu____2747 =
                                        let uu____2750 =
                                          mktac1 () () "apply"
                                            (fun a469  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a469)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____2751 =
                                          let uu____2754 =
                                            mktac1 () () "apply_raw"
                                              (fun a470  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a470)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____2755 =
                                            let uu____2758 =
                                              mktac1 () () "apply_lemma"
                                                (fun a471  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a471)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____2759 =
                                              let uu____2762 =
                                                let uu____2763 =
                                                  FStar_Syntax_Embeddings.embed_tuple2
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a472  ->
                                                     fun a473  ->
                                                       fun a474  ->
                                                         fun a475  ->
                                                           fun a476  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2772
                                                                    ->
                                                                   fun
                                                                    uu____2773
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a472 a473 a474
                                                               a475 a476)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____2763)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2780 =
                                                let uu____2783 =
                                                  mktac2 () () () "__seq"
                                                    (fun a477  ->
                                                       fun a478  ->
                                                         (Obj.magic
                                                            FStar_Tactics_Basic.seq)
                                                           a477 a478)
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
                                                let uu____2784 =
                                                  let uu____2787 =
                                                    mktac1 () ()
                                                      "set_options"
                                                      (fun a479  ->
                                                         (Obj.magic
                                                            FStar_Tactics_Basic.set_options)
                                                           a479)
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.unembed_string)
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.embed_unit)
                                                      FStar_Syntax_Syntax.t_unit
                                                     in
                                                  let uu____2788 =
                                                    let uu____2791 =
                                                      mktac1 () () "tc"
                                                        (fun a480  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a480)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____2792 =
                                                      let uu____2795 =
                                                        mktac1 () ()
                                                          "unshelve"
                                                          (fun a481  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a481)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____2796 =
                                                        let uu____2799 =
                                                          mktac2 () () ()
                                                            "unquote"
                                                            (fun a482  ->
                                                               fun a483  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a482 a483)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____2800 =
                                                          let uu____2803 =
                                                            mktac1 () ()
                                                              "prune"
                                                              (fun a484  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a484)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____2804 =
                                                            let uu____2807 =
                                                              mktac1 () ()
                                                                "addns"
                                                                (fun a485  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a485)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____2808 =
                                                              let uu____2811
                                                                =
                                                                mktac1 () ()
                                                                  "print"
                                                                  (fun a486 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print)
                                                                    a486)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____2812
                                                                =
                                                                let uu____2815
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "debug"
                                                                    (
                                                                    fun a487 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.debug)
                                                                    a487)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____2816
                                                                  =
                                                                  let uu____2819
                                                                    =
                                                                    mktac1 ()
                                                                    () "dump"
                                                                    (fun a488
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a488)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                  let uu____2820
                                                                    =
                                                                    let uu____2823
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "dump1"
                                                                    (fun a489
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a489)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2824
                                                                    =
                                                                    let uu____2827
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a490
                                                                     ->
                                                                    fun a491 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a490 a491)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2828
                                                                    =
                                                                    let uu____2831
                                                                    =
                                                                    let uu____2832
                                                                    =
                                                                    let uu____2843
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_tuple2
                                                                    FStar_Syntax_Embeddings.unembed_bool
                                                                    FStar_Syntax_Embeddings.unembed_int
                                                                     in
                                                                    unembed_tactic_1
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    uu____2843
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__topdown_rewrite"
                                                                    (fun a492
                                                                     ->
                                                                    fun a493 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.topdown_rewrite)
                                                                    a492 a493)
                                                                    (Obj.magic
                                                                    uu____2832)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2862
                                                                    =
                                                                    let uu____2865
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "trefl"
                                                                    (fun a494
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    a494)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2866
                                                                    =
                                                                    let uu____2869
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "later"
                                                                    (fun a495
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    a495)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2870
                                                                    =
                                                                    let uu____2873
                                                                    =
                                                                    mktac1 ()
                                                                    () "dup"
                                                                    (fun a496
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    a496)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2874
                                                                    =
                                                                    let uu____2877
                                                                    =
                                                                    mktac1 ()
                                                                    () "flip"
                                                                    (fun a497
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    a497)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2878
                                                                    =
                                                                    let uu____2881
                                                                    =
                                                                    mktac1 ()
                                                                    () "qed"
                                                                    (fun a498
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    a498)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2882
                                                                    =
                                                                    let uu____2885
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "dismiss"
                                                                    (fun a499
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dismiss)
                                                                    a499)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2886
                                                                    =
                                                                    let uu____2889
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "tadmit"
                                                                    (fun a500
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.tadmit)
                                                                    a500)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2890
                                                                    =
                                                                    let uu____2893
                                                                    =
                                                                    let uu____2894
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_tuple2
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2901
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "cases"
                                                                    (fun a501
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a501)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2894)
                                                                    uu____2901
                                                                     in
                                                                    let uu____2908
                                                                    =
                                                                    let uu____2911
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "top_env"
                                                                    (fun a502
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    a502)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2912
                                                                    =
                                                                    let uu____2915
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_env"
                                                                    (fun a503
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    a503)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2916
                                                                    =
                                                                    let uu____2919
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_goal"
                                                                    (fun a504
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    a504)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2920
                                                                    =
                                                                    let uu____2923
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_witness"
                                                                    (fun a505
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    a505)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2924
                                                                    =
                                                                    let uu____2927
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "inspect"
                                                                    (fun a506
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.inspect)
                                                                    a506)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term_view)
                                                                    FStar_Reflection_Data.fstar_refl_term_view
                                                                     in
                                                                    let uu____2928
                                                                    =
                                                                    let uu____2931
                                                                    =
                                                                    mktac1 ()
                                                                    () "pack"
                                                                    (fun a507
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pack)
                                                                    a507)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term_view)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2932
                                                                    =
                                                                    let uu____2935
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "fresh"
                                                                    (fun a508
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh)
                                                                    a508)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2936
                                                                    =
                                                                    let uu____2939
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "ngoals"
                                                                    (fun a509
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals)
                                                                    a509)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2940
                                                                    =
                                                                    let uu____2943
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "ngoals_smt"
                                                                    (fun a510
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals_smt)
                                                                    a510)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2944
                                                                    =
                                                                    let uu____2947
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "is_guard"
                                                                    (fun a511
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    a511)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2948
                                                                    =
                                                                    let uu____2951
                                                                    =
                                                                    let uu____2952
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Embeddings.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "uvar_env"
                                                                    (fun a512
                                                                     ->
                                                                    fun a513 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a512 a513)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2952)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2961
                                                                    =
                                                                    let uu____2964
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "unify"
                                                                    (fun a514
                                                                     ->
                                                                    fun a515 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a514 a515)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2965
                                                                    =
                                                                    let uu____2968
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "launch_process"
                                                                    (fun a516
                                                                     ->
                                                                    fun a517 
                                                                    ->
                                                                    fun a518 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a516 a517
                                                                    a518)
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
                                                                    let uu____2969
                                                                    =
                                                                    let uu____2972
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "fresh_bv_named"
                                                                    (fun a519
                                                                     ->
                                                                    fun a520 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_bv_named)
                                                                    a519 a520)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_bv)
                                                                    FStar_Syntax_Syntax.t_bv
                                                                     in
                                                                    let uu____2973
                                                                    =
                                                                    let uu____2976
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "change"
                                                                    (fun a521
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.change)
                                                                    a521)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2977
                                                                    =
                                                                    let uu____2980
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "get_guard_policy"
                                                                    (fun a522
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.get_guard_policy)
                                                                    a522)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.embed_guard_policy)
                                                                    FStar_Tactics_Embedding.t_guard_policy
                                                                     in
                                                                    let uu____2981
                                                                    =
                                                                    let uu____2984
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "set_guard_policy"
                                                                    (fun a523
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.set_guard_policy)
                                                                    a523)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    [uu____2984;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____2980
                                                                    ::
                                                                    uu____2981
                                                                     in
                                                                    uu____2976
                                                                    ::
                                                                    uu____2977
                                                                     in
                                                                    uu____2972
                                                                    ::
                                                                    uu____2973
                                                                     in
                                                                    uu____2968
                                                                    ::
                                                                    uu____2969
                                                                     in
                                                                    uu____2964
                                                                    ::
                                                                    uu____2965
                                                                     in
                                                                    uu____2951
                                                                    ::
                                                                    uu____2961
                                                                     in
                                                                    uu____2947
                                                                    ::
                                                                    uu____2948
                                                                     in
                                                                    uu____2943
                                                                    ::
                                                                    uu____2944
                                                                     in
                                                                    uu____2939
                                                                    ::
                                                                    uu____2940
                                                                     in
                                                                    uu____2935
                                                                    ::
                                                                    uu____2936
                                                                     in
                                                                    uu____2931
                                                                    ::
                                                                    uu____2932
                                                                     in
                                                                    uu____2927
                                                                    ::
                                                                    uu____2928
                                                                     in
                                                                    uu____2923
                                                                    ::
                                                                    uu____2924
                                                                     in
                                                                    uu____2919
                                                                    ::
                                                                    uu____2920
                                                                     in
                                                                    uu____2915
                                                                    ::
                                                                    uu____2916
                                                                     in
                                                                    uu____2911
                                                                    ::
                                                                    uu____2912
                                                                     in
                                                                    uu____2893
                                                                    ::
                                                                    uu____2908
                                                                     in
                                                                    uu____2889
                                                                    ::
                                                                    uu____2890
                                                                     in
                                                                    uu____2885
                                                                    ::
                                                                    uu____2886
                                                                     in
                                                                    uu____2881
                                                                    ::
                                                                    uu____2882
                                                                     in
                                                                    uu____2877
                                                                    ::
                                                                    uu____2878
                                                                     in
                                                                    uu____2873
                                                                    ::
                                                                    uu____2874
                                                                     in
                                                                    uu____2869
                                                                    ::
                                                                    uu____2870
                                                                     in
                                                                    uu____2865
                                                                    ::
                                                                    uu____2866
                                                                     in
                                                                    uu____2831
                                                                    ::
                                                                    uu____2862
                                                                     in
                                                                    uu____2827
                                                                    ::
                                                                    uu____2828
                                                                     in
                                                                    uu____2823
                                                                    ::
                                                                    uu____2824
                                                                     in
                                                                  uu____2819
                                                                    ::
                                                                    uu____2820
                                                                   in
                                                                uu____2815 ::
                                                                  uu____2816
                                                                 in
                                                              uu____2811 ::
                                                                uu____2812
                                                               in
                                                            uu____2807 ::
                                                              uu____2808
                                                             in
                                                          uu____2803 ::
                                                            uu____2804
                                                           in
                                                        uu____2799 ::
                                                          uu____2800
                                                         in
                                                      uu____2795 ::
                                                        uu____2796
                                                       in
                                                    uu____2791 :: uu____2792
                                                     in
                                                  uu____2787 :: uu____2788
                                                   in
                                                uu____2783 :: uu____2784  in
                                              uu____2762 :: uu____2780  in
                                            uu____2758 :: uu____2759  in
                                          uu____2754 :: uu____2755  in
                                        uu____2750 :: uu____2751  in
                                      uu____2746 :: uu____2747  in
                                    uu____2742 :: uu____2743  in
                                  uu____2738 :: uu____2739  in
                                uu____2734 :: uu____2735  in
                              uu____2730 :: uu____2731  in
                            uu____2726 :: uu____2727  in
                          uu____2722 :: uu____2723  in
                        uu____2718 :: uu____2719  in
                      uu____2714 :: uu____2715  in
                    uu____2701 :: uu____2711  in
                  uu____2688 :: uu____2698  in
                uu____2675 :: uu____2685  in
              uu____2657 :: uu____2672  in
            uu____2653 :: uu____2654  in
          uu____2636 :: uu____2650  in
        uu____2632 :: uu____2633  in
      uu____2626 :: uu____2629  in
    FStar_List.append uu____2623
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
               let uu____3014 =
                 let uu____3015 =
                   let uu____3016 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____3016]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____3015  in
               uu____3014 FStar_Pervasives_Native.None rng  in
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
             let uu____3045 =
               let uu____3046 =
                 let uu____3047 =
                   let uu____3048 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____3048  in
                 [uu____3047]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3046  in
             uu____3045 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____3055 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____3055
            then
              let uu____3056 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____3056
            else ());
           (let result =
              let uu____3059 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____3059 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____3063 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____3063
             then
               let uu____3064 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____3064
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____3109 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3109
                   (fun uu____3113  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____3136 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3136
                   (fun uu____3140  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____3153 =
                   let uu____3158 =
                     let uu____3159 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____3159
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____3158)  in
                 FStar_Errors.raise_error uu____3153
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____3168 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
        uu____3168

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____3224  ->
             match uu____3224 with
             | (r,uu____3244,uv,uu____3246,ty,rng) ->
                 let uu____3249 =
                   let uu____3250 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____3251 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____3250 uu____3251 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____3249, rng)) is
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
        (let uu____3300 = FStar_ST.op_Bang tacdbg  in
         if uu____3300
         then
           let uu____3320 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____3320
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____3324 = FStar_ST.op_Bang tacdbg  in
          if uu____3324
          then
            let uu____3344 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____3344
          else ());
         (let uu____3346 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____3346 with
          | (uu____3359,uu____3360,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic1
                   in
                let uu____3367 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____3367 with
                | (env1,uu____3381) ->
                    let env2 =
                      let uu___61_3387 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___61_3387.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___61_3387.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___61_3387.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___61_3387.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___61_3387.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___61_3387.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___61_3387.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___61_3387.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___61_3387.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___61_3387.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___61_3387.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___61_3387.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___61_3387.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___61_3387.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___61_3387.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___61_3387.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___61_3387.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___61_3387.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___61_3387.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___61_3387.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___61_3387.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___61_3387.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___61_3387.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___61_3387.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___61_3387.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___61_3387.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___61_3387.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___61_3387.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___61_3387.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___61_3387.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___61_3387.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___61_3387.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___61_3387.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___61_3387.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___61_3387.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let env3 =
                      let uu___62_3389 = env2  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___62_3389.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___62_3389.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___62_3389.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___62_3389.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___62_3389.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___62_3389.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___62_3389.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___62_3389.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___62_3389.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___62_3389.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___62_3389.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___62_3389.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___62_3389.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___62_3389.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___62_3389.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___62_3389.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___62_3389.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___62_3389.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___62_3389.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes = true;
                        FStar_TypeChecker_Env.failhard =
                          (uu___62_3389.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___62_3389.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___62_3389.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___62_3389.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___62_3389.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___62_3389.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___62_3389.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___62_3389.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___62_3389.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___62_3389.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___62_3389.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___62_3389.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___62_3389.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___62_3389.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___62_3389.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___62_3389.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____3390 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ  in
                    (match uu____3390 with
                     | (ps,w) ->
                         ((let uu____3404 = FStar_ST.op_Bang tacdbg  in
                           if uu____3404
                           then
                             let uu____3424 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____3424
                           else ());
                          (let uu____3426 =
                             FStar_Util.record_time
                               (fun uu____3436  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____3426 with
                           | (res,ms) ->
                               ((let uu____3450 = FStar_ST.op_Bang tacdbg  in
                                 if uu____3450
                                 then
                                   let uu____3470 =
                                     FStar_Syntax_Print.term_to_string
                                       tactic1
                                      in
                                   let uu____3471 =
                                     FStar_Util.string_of_int ms  in
                                   let uu____3472 =
                                     FStar_Syntax_Print.lid_to_string
                                       env3.FStar_TypeChecker_Env.curmodule
                                      in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____3470 uu____3471 uu____3472
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____3480,ps1) ->
                                     ((let uu____3483 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____3483
                                       then
                                         let uu____3503 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____3503
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____3510 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____3510
                                           then
                                             let uu____3511 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____3511
                                              then ()
                                              else
                                                (let uu____3513 =
                                                   let uu____3514 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____3514
                                                    in
                                                 failwith uu____3513))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___63_3517 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___63_3517.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___63_3517.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___63_3517.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____3519 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env3 g1
                                            in
                                         FStar_All.pipe_right uu____3519
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____3526 =
                                         let uu____3527 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____3527 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____3526 "at the time of failure");
                                      (let uu____3528 =
                                         let uu____3533 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____3533)
                                          in
                                       FStar_Errors.raise_error uu____3528
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____3543 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____3547 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____3551 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3600 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3636 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3686 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3724 . 'Auu____3724 -> 'Auu____3724 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3743 = FStar_Syntax_Util.head_and_args t  in
        match uu____3743 with
        | (hd1,args) ->
            let uu____3780 =
              let uu____3793 =
                let uu____3794 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3794.FStar_Syntax_Syntax.n  in
              (uu____3793, args)  in
            (match uu____3780 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3807))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3870 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3870 with
                       | (gs,uu____3878) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3885 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3885 with
                       | (gs,uu____3893) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3944 =
                        let uu____3951 =
                          let uu____3954 =
                            let uu____3955 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3955
                             in
                          [uu____3954]  in
                        (FStar_Syntax_Util.t_true, uu____3951)  in
                      Simplified uu____3944
                  | Both  ->
                      let uu____3966 =
                        let uu____3979 =
                          let uu____3982 =
                            let uu____3983 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3983
                             in
                          [uu____3982]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3979)  in
                      Dual uu____3966
                  | Neg  -> Simplified (assertion, []))
             | uu____4004 -> Unchanged t)
  
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
    fun uu___59_4084  ->
      match uu___59_4084 with
      | Unchanged t -> let uu____4090 = f t  in Unchanged uu____4090
      | Simplified (t,gs) ->
          let uu____4097 = let uu____4104 = f t  in (uu____4104, gs)  in
          Simplified uu____4097
      | Dual (tn,tp,gs) ->
          let uu____4114 =
            let uu____4123 = f tn  in
            let uu____4124 = f tp  in (uu____4123, uu____4124, gs)  in
          Dual uu____4114
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____4178 = f t1 t2  in Unchanged uu____4178
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____4190 = let uu____4197 = f t1 t2  in (uu____4197, gs)
               in
            Simplified uu____4190
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____4211 = let uu____4218 = f t1 t2  in (uu____4218, gs)
               in
            Simplified uu____4211
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____4237 =
              let uu____4244 = f t1 t2  in
              (uu____4244, (FStar_List.append gs1 gs2))  in
            Simplified uu____4237
        | uu____4247 ->
            let uu____4256 = explode x  in
            (match uu____4256 with
             | (n1,p1,gs1) ->
                 let uu____4274 = explode y  in
                 (match uu____4274 with
                  | (n2,p2,gs2) ->
                      let uu____4292 =
                        let uu____4301 = f n1 n2  in
                        let uu____4302 = f p1 p2  in
                        (uu____4301, uu____4302, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____4292))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____4367 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____4367
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____4410  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____4444 =
              let uu____4445 = FStar_Syntax_Subst.compress t  in
              uu____4445.FStar_Syntax_Syntax.n  in
            match uu____4444 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____4457 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____4457 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____4481 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____4481 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4499;
                   FStar_Syntax_Syntax.vars = uu____4500;_},(p,uu____4502)::
                 (q,uu____4504)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____4544 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4544
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____4547 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____4547 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4553 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4553.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4557;
                   FStar_Syntax_Syntax.vars = uu____4558;_},(p,uu____4560)::
                 (q,uu____4562)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4602 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4602
                   in
                let xq =
                  let uu____4604 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4604
                   in
                let r1 =
                  let uu____4606 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4606 p  in
                let r2 =
                  let uu____4608 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4608 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4611,Unchanged uu____4612) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4622 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4622.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4625 ->
                     let uu____4630 = explode r1  in
                     (match uu____4630 with
                      | (pn,pp,gs1) ->
                          let uu____4648 = explode r2  in
                          (match uu____4648 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4669 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4670 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4669
                                   uu____4670
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4722  ->
                       fun r  ->
                         match uu____4722 with
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
                let uu____4840 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4840 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4874  ->
                            match uu____4874 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4888 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___64_4912 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___64_4912.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___64_4912.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4888 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4932 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4932.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4978 = traverse f pol e t1  in
                let uu____4983 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4983 uu____4978
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___65_5021 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___65_5021.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___65_5021.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____5028 =
                f pol e
                  (let uu___66_5032 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___66_5032.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___66_5032.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____5028
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___67_5042 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___67_5042.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___67_5042.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____5043 = explode rp  in
              (match uu____5043 with
               | (uu____5052,p',gs') ->
                   Dual
                     ((let uu___68_5066 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___68_5066.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___68_5066.FStar_Syntax_Syntax.vars)
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
      (let uu____5101 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5101);
      (let uu____5122 = FStar_ST.op_Bang tacdbg  in
       if uu____5122
       then
         let uu____5142 =
           let uu____5143 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____5143
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____5144 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____5142
           uu____5144
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____5173 =
         let uu____5180 = traverse by_tactic_interp Pos env goal  in
         match uu____5180 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____5198 -> failwith "no"  in
       match uu____5173 with
       | (t',gs) ->
           ((let uu____5220 = FStar_ST.op_Bang tacdbg  in
             if uu____5220
             then
               let uu____5240 =
                 let uu____5241 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____5241
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____5242 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____5240 uu____5242
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5289  ->
                    fun g  ->
                      match uu____5289 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5334 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____5334 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5337 =
                                  let uu____5342 =
                                    let uu____5343 =
                                      FStar_Syntax_Print.term_to_string
                                        g.FStar_Tactics_Types.goal_ty
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5343
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5342)
                                   in
                                FStar_Errors.raise_error uu____5337
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5346 = FStar_ST.op_Bang tacdbg  in
                            if uu____5346
                            then
                              let uu____5366 = FStar_Util.string_of_int n1
                                 in
                              let uu____5367 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5366 uu____5367
                            else ());
                           (let gt' =
                              let uu____5370 =
                                let uu____5371 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____5371
                                 in
                              FStar_TypeChecker_Util.label uu____5370
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____5386 = s1  in
             match uu____5386 with
             | (uu____5407,gs1) ->
                 let uu____5425 =
                   let uu____5432 = FStar_Options.peek ()  in
                   (env, t', uu____5432)  in
                 uu____5425 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____5443 =
        let uu____5444 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____5444  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____5443 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____5445 =
      let uu____5446 =
        let uu____5447 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____5448 =
          let uu____5451 = FStar_Syntax_Syntax.as_arg a  in [uu____5451]  in
        uu____5447 :: uu____5448  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____5446  in
    uu____5445 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____5464 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____5464);
        (let uu____5484 =
           let uu____5491 = reify_tactic tau  in
           run_tactic_on_typ uu____5491 env typ  in
         match uu____5484 with
         | (gs,w) ->
             let uu____5498 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5502 =
                      let uu____5503 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5503  in
                    Prims.op_Negation uu____5502) gs
                in
             if uu____5498
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
      (let uu____5518 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5518);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____5539 =
         let uu____5546 = reify_tactic tau  in
         run_tactic_on_typ uu____5546 env typ  in
       match uu____5539 with
       | (gs,w) ->
           ((let uu____5556 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5560 =
                      let uu____5561 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5561  in
                    Prims.op_Negation uu____5560) gs
                in
             if uu____5556
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
             let uu____5566 =
               let uu____5571 =
                 FStar_Syntax_Embeddings.unembed_list
                   FStar_Reflection_Embeddings.unembed_sigelt
                  in
               uu____5571 w1  in
             FStar_All.pipe_left FStar_Util.must uu____5566)))
  