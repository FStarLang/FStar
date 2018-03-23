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
  
let mk_tactic_interpretation_13 :
  'r 't1 't10 't11 't12 't13 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.bool ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 -> 't12 -> 't13 -> 'r FStar_Tactics_Basic.tac)
        ->
        't1 FStar_Syntax_Embeddings.unembedder ->
          't2 FStar_Syntax_Embeddings.unembedder ->
            't3 FStar_Syntax_Embeddings.unembedder ->
              't4 FStar_Syntax_Embeddings.unembedder ->
                't5 FStar_Syntax_Embeddings.unembedder ->
                  't6 FStar_Syntax_Embeddings.unembedder ->
                    't7 FStar_Syntax_Embeddings.unembedder ->
                      't8 FStar_Syntax_Embeddings.unembedder ->
                        't9 FStar_Syntax_Embeddings.unembedder ->
                          't10 FStar_Syntax_Embeddings.unembedder ->
                            't11 FStar_Syntax_Embeddings.unembedder ->
                              't12 FStar_Syntax_Embeddings.unembedder ->
                                't13 FStar_Syntax_Embeddings.unembedder ->
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
      fun unembed_t1  ->
        fun unembed_t2  ->
          fun unembed_t3  ->
            fun unembed_t4  ->
              fun unembed_t5  ->
                fun unembed_t6  ->
                  fun unembed_t7  ->
                    fun unembed_t8  ->
                      fun unembed_t9  ->
                        fun unembed_t10  ->
                          fun unembed_t11  ->
                            fun unembed_t12  ->
                              fun unembed_t13  ->
                                fun embed_r  ->
                                  fun t_r  ->
                                    fun nm  ->
                                      fun psc  ->
                                        fun args  ->
                                          match args with
                                          | (a1,uu____2134)::(a2,uu____2136)::
                                              (a3,uu____2138)::(a4,uu____2140)::
                                              (a5,uu____2142)::(a6,uu____2144)::
                                              (a7,uu____2146)::(a8,uu____2148)::
                                              (a9,uu____2150)::(a10,uu____2152)::
                                              (a11,uu____2154)::(a12,uu____2156)::
                                              (a13,uu____2158)::(embedded_state,uu____2160)::[]
                                              ->
                                              let uu____2307 =
                                                FStar_Tactics_Embedding.unembed_proofstate
                                                  embedded_state
                                                 in
                                              FStar_Util.bind_opt uu____2307
                                                (fun ps  ->
                                                   let ps1 =
                                                     FStar_Tactics_Types.set_ps_psc
                                                       psc ps
                                                      in
                                                   FStar_Tactics_Basic.log
                                                     ps1
                                                     (fun uu____2320  ->
                                                        let uu____2321 =
                                                          FStar_Ident.string_of_lid
                                                            nm
                                                           in
                                                        let uu____2322 =
                                                          FStar_Syntax_Print.term_to_string
                                                            embedded_state
                                                           in
                                                        FStar_Util.print2
                                                          "Reached %s, goals are: %s\n"
                                                          uu____2321
                                                          uu____2322);
                                                   (let uu____2323 =
                                                      unembed_t1 a1  in
                                                    FStar_Util.bind_opt
                                                      uu____2323
                                                      (fun a14  ->
                                                         let uu____2331 =
                                                           unembed_t2 a2  in
                                                         FStar_Util.bind_opt
                                                           uu____2331
                                                           (fun a21  ->
                                                              let uu____2339
                                                                =
                                                                unembed_t3 a3
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____2339
                                                                (fun a31  ->
                                                                   let uu____2347
                                                                    =
                                                                    unembed_t4
                                                                    a4  in
                                                                   FStar_Util.bind_opt
                                                                    uu____2347
                                                                    (fun a41 
                                                                    ->
                                                                    let uu____2355
                                                                    =
                                                                    unembed_t5
                                                                    a5  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2355
                                                                    (fun a51 
                                                                    ->
                                                                    let uu____2363
                                                                    =
                                                                    unembed_t6
                                                                    a6  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2363
                                                                    (fun a61 
                                                                    ->
                                                                    let uu____2371
                                                                    =
                                                                    unembed_t7
                                                                    a7  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2371
                                                                    (fun a71 
                                                                    ->
                                                                    let uu____2379
                                                                    =
                                                                    unembed_t8
                                                                    a8  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2379
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____2387
                                                                    =
                                                                    unembed_t9
                                                                    a9  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2387
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____2395
                                                                    =
                                                                    unembed_t10
                                                                    a10  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2395
                                                                    (fun a101
                                                                     ->
                                                                    let uu____2403
                                                                    =
                                                                    unembed_t11
                                                                    a11  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2403
                                                                    (fun a111
                                                                     ->
                                                                    let uu____2411
                                                                    =
                                                                    unembed_t12
                                                                    a12  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2411
                                                                    (fun a121
                                                                     ->
                                                                    let uu____2419
                                                                    =
                                                                    unembed_t13
                                                                    a13  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2419
                                                                    (fun a131
                                                                     ->
                                                                    let res =
                                                                    let uu____2431
                                                                    =
                                                                    t a14 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131  in
                                                                    FStar_Tactics_Basic.run
                                                                    uu____2431
                                                                    ps1  in
                                                                    let uu____2434
                                                                    =
                                                                    let uu____2435
                                                                    =
                                                                    FStar_TypeChecker_Normalize.psc_range
                                                                    psc  in
                                                                    let uu____2436
                                                                    =
                                                                    FStar_Tactics_Embedding.embed_result
                                                                    embed_r
                                                                    t_r  in
                                                                    uu____2436
                                                                    uu____2435
                                                                    res  in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____2434)))))))))))))))
                                          | uu____2450 ->
                                              let uu____2451 =
                                                let uu____2452 =
                                                  FStar_Ident.string_of_lid
                                                    nm
                                                   in
                                                let uu____2453 =
                                                  FStar_Syntax_Print.args_to_string
                                                    args
                                                   in
                                                FStar_Util.format2
                                                  "Unexpected application of tactic primitive %s %s"
                                                  uu____2452 uu____2453
                                                 in
                                              failwith uu____2451
  
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
  fun uu____2539  ->
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
      | (ps,uu____2991)::[] ->
          let uu____3008 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____3008
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____3016 =
                 let uu____3017 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____3018 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____3017
                   uu____3018
                  in
               FStar_Pervasives_Native.Some uu____3016)
      | uu____3019 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____3023 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____3023;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____3036)::[] ->
          let uu____3053 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____3053
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____3061 =
                 let uu____3062 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____3063 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____3062
                   uu____3063
                  in
               FStar_Pervasives_Native.Some uu____3061)
      | uu____3064 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____3068 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____3068;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____3085)::[] ->
          let uu____3102 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____3102
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____3115 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____3132)::(r,uu____3134)::[] ->
          let uu____3161 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____3161
            (fun ps1  ->
               let uu____3167 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____3167
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____3175 =
                      let uu____3176 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____3176 ps'
                       in
                    FStar_Pervasives_Native.Some uu____3175))
      | uu____3177 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____3192)::(b,uu____3194)::[] ->
          let uu____3221 = FStar_Reflection_Embeddings.unembed_env env_t  in
          FStar_Util.bind_opt uu____3221
            (fun env  ->
               let uu____3227 = FStar_Reflection_Embeddings.unembed_binder b
                  in
               FStar_Util.bind_opt uu____3227
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____3235 =
                      FStar_Reflection_Embeddings.embed_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____3235))
      | uu____3236 -> failwith "Unexpected application of push_binder"  in
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
      let uu___58_3252 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___58_3252.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___58_3252.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____3259 =
      let uu____3262 =
        mktac2 () () () "fail"
          (fun a438  ->
             fun a439  ->
               (Obj.magic (fun uu____3264  -> FStar_Tactics_Basic.fail)) a438
                 a439) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____3265 =
        let uu____3268 =
          mktac1 () () "trivial"
            (fun a440  -> (Obj.magic FStar_Tactics_Basic.trivial) a440)
            (Obj.magic FStar_Syntax_Embeddings.unembed_unit)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____3269 =
          let uu____3272 =
            let uu____3273 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a441  ->
                 fun a442  ->
                   (Obj.magic (fun uu____3279  -> FStar_Tactics_Basic.trytac))
                     a441 a442) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____3273)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____3286 =
            let uu____3289 =
              mktac1 () () "intro"
                (fun a443  -> (Obj.magic FStar_Tactics_Basic.intro) a443)
                (Obj.magic FStar_Syntax_Embeddings.unembed_unit)
                (Obj.magic FStar_Reflection_Embeddings.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____3290 =
              let uu____3293 =
                let uu____3294 =
                  FStar_Syntax_Embeddings.embed_tuple2
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____3301 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac1 () () "intro_rec"
                  (fun a444  ->
                     (Obj.magic FStar_Tactics_Basic.intro_rec) a444)
                  (Obj.magic FStar_Syntax_Embeddings.unembed_unit)
                  (Obj.magic uu____3294) uu____3301
                 in
              let uu____3308 =
                let uu____3311 =
                  let uu____3312 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "norm"
                    (fun a445  -> (Obj.magic FStar_Tactics_Basic.norm) a445)
                    (Obj.magic uu____3312)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____3321 =
                  let uu____3324 =
                    let uu____3325 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step
                       in
                    mktac3 () () () () "norm_term_env"
                      (fun a446  ->
                         fun a447  ->
                           fun a448  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a446 a447 a448)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_env)
                      (Obj.magic uu____3325)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_term)
                      (Obj.magic FStar_Reflection_Embeddings.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____3334 =
                    let uu____3337 =
                      let uu____3338 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "norm_binder_type"
                        (fun a449  ->
                           fun a450  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a449 a450) (Obj.magic uu____3338)
                        (Obj.magic FStar_Reflection_Embeddings.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____3347 =
                      let uu____3350 =
                        mktac2 () () () "rename_to"
                          (fun a451  ->
                             fun a452  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a451
                                 a452)
                          (Obj.magic
                             FStar_Reflection_Embeddings.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit
                         in
                      let uu____3351 =
                        let uu____3354 =
                          mktac1 () () "binder_retype"
                            (fun a453  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a453)
                            (Obj.magic
                               FStar_Reflection_Embeddings.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____3355 =
                          let uu____3358 =
                            mktac1 () () "revert"
                              (fun a454  ->
                                 (Obj.magic FStar_Tactics_Basic.revert) a454)
                              (Obj.magic FStar_Syntax_Embeddings.unembed_unit)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____3359 =
                            let uu____3362 =
                              mktac1 () () "clear_top"
                                (fun a455  ->
                                   (Obj.magic FStar_Tactics_Basic.clear_top)
                                     a455)
                                (Obj.magic
                                   FStar_Syntax_Embeddings.unembed_unit)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____3363 =
                              let uu____3366 =
                                mktac1 () () "clear"
                                  (fun a456  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a456)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit
                                 in
                              let uu____3367 =
                                let uu____3370 =
                                  mktac1 () () "rewrite"
                                    (fun a457  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a457)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                let uu____3371 =
                                  let uu____3374 =
                                    mktac1 () () "smt"
                                      (fun a458  ->
                                         (Obj.magic FStar_Tactics_Basic.smt)
                                           a458)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.unembed_unit)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____3375 =
                                    let uu____3378 =
                                      mktac1 () () "refine_intro"
                                        (fun a459  ->
                                           (Obj.magic
                                              FStar_Tactics_Basic.refine_intro)
                                             a459)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.unembed_unit)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____3379 =
                                      let uu____3382 =
                                        mktac2 () () () "t_exact"
                                          (fun a460  ->
                                             fun a461  ->
                                               (Obj.magic
                                                  FStar_Tactics_Basic.t_exact)
                                                 a460 a461)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit
                                         in
                                      let uu____3383 =
                                        let uu____3386 =
                                          mktac1 () () "apply"
                                            (fun a462  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a462)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____3387 =
                                          let uu____3390 =
                                            mktac1 () () "apply_raw"
                                              (fun a463  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a463)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____3391 =
                                            let uu____3394 =
                                              mktac1 () () "apply_lemma"
                                                (fun a464  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a464)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____3395 =
                                              let uu____3398 =
                                                let uu____3399 =
                                                  FStar_Syntax_Embeddings.embed_tuple2
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a465  ->
                                                     fun a466  ->
                                                       fun a467  ->
                                                         fun a468  ->
                                                           fun a469  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____3408
                                                                    ->
                                                                   fun
                                                                    uu____3409
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a465 a466 a467
                                                               a468 a469)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____3399)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____3416 =
                                                let uu____3419 =
                                                  mktac2 () () () "__seq"
                                                    (fun a470  ->
                                                       fun a471  ->
                                                         (Obj.magic
                                                            FStar_Tactics_Basic.seq)
                                                           a470 a471)
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
                                                let uu____3420 =
                                                  let uu____3423 =
                                                    mktac1 () ()
                                                      "set_options"
                                                      (fun a472  ->
                                                         (Obj.magic
                                                            FStar_Tactics_Basic.set_options)
                                                           a472)
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.unembed_string)
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.embed_unit)
                                                      FStar_Syntax_Syntax.t_unit
                                                     in
                                                  let uu____3424 =
                                                    let uu____3427 =
                                                      mktac1 () () "tc"
                                                        (fun a473  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a473)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____3428 =
                                                      let uu____3431 =
                                                        mktac1 () ()
                                                          "unshelve"
                                                          (fun a474  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a474)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____3432 =
                                                        let uu____3435 =
                                                          mktac2 () () ()
                                                            "unquote"
                                                            (fun a475  ->
                                                               fun a476  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a475 a476)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____3436 =
                                                          let uu____3439 =
                                                            mktac1 () ()
                                                              "prune"
                                                              (fun a477  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a477)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____3440 =
                                                            let uu____3443 =
                                                              mktac1 () ()
                                                                "addns"
                                                                (fun a478  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a478)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____3444 =
                                                              let uu____3447
                                                                =
                                                                mktac1 () ()
                                                                  "print"
                                                                  (fun a479 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print)
                                                                    a479)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____3448
                                                                =
                                                                let uu____3451
                                                                  =
                                                                  mktac1 ()
                                                                    () "dump"
                                                                    (
                                                                    fun a480 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a480)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____3452
                                                                  =
                                                                  let uu____3455
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "dump1"
                                                                    (fun a481
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a481)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                  let uu____3456
                                                                    =
                                                                    let uu____3459
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a482
                                                                     ->
                                                                    fun a483 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a482 a483)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3460
                                                                    =
                                                                    let uu____3463
                                                                    =
                                                                    let uu____3464
                                                                    =
                                                                    let uu____3475
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_tuple2
                                                                    FStar_Syntax_Embeddings.unembed_bool
                                                                    FStar_Syntax_Embeddings.unembed_int
                                                                     in
                                                                    unembed_tactic_1
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    uu____3475
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__topdown_rewrite"
                                                                    (fun a484
                                                                     ->
                                                                    fun a485 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.topdown_rewrite)
                                                                    a484 a485)
                                                                    (Obj.magic
                                                                    uu____3464)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3494
                                                                    =
                                                                    let uu____3497
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "trefl"
                                                                    (fun a486
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    a486)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3498
                                                                    =
                                                                    let uu____3501
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "later"
                                                                    (fun a487
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    a487)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3502
                                                                    =
                                                                    let uu____3505
                                                                    =
                                                                    mktac1 ()
                                                                    () "dup"
                                                                    (fun a488
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    a488)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3506
                                                                    =
                                                                    let uu____3509
                                                                    =
                                                                    mktac1 ()
                                                                    () "flip"
                                                                    (fun a489
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    a489)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3510
                                                                    =
                                                                    let uu____3513
                                                                    =
                                                                    mktac1 ()
                                                                    () "qed"
                                                                    (fun a490
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    a490)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3514
                                                                    =
                                                                    let uu____3517
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "dismiss"
                                                                    (fun a491
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dismiss)
                                                                    a491)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3518
                                                                    =
                                                                    let uu____3521
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "tadmit"
                                                                    (fun a492
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.tadmit)
                                                                    a492)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3522
                                                                    =
                                                                    let uu____3525
                                                                    =
                                                                    let uu____3526
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_tuple2
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____3533
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "cases"
                                                                    (fun a493
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a493)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    uu____3526)
                                                                    uu____3533
                                                                     in
                                                                    let uu____3540
                                                                    =
                                                                    let uu____3543
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "top_env"
                                                                    (fun a494
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    a494)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____3544
                                                                    =
                                                                    let uu____3547
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_env"
                                                                    (fun a495
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    a495)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____3548
                                                                    =
                                                                    let uu____3551
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_goal"
                                                                    (fun a496
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    a496)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____3552
                                                                    =
                                                                    let uu____3555
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_witness"
                                                                    (fun a497
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    a497)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____3556
                                                                    =
                                                                    let uu____3559
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "inspect"
                                                                    (fun a498
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.inspect)
                                                                    a498)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term_view)
                                                                    FStar_Reflection_Data.fstar_refl_term_view
                                                                     in
                                                                    let uu____3560
                                                                    =
                                                                    let uu____3563
                                                                    =
                                                                    mktac1 ()
                                                                    () "pack"
                                                                    (fun a499
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pack)
                                                                    a499)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term_view)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____3564
                                                                    =
                                                                    let uu____3567
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "fresh"
                                                                    (fun a500
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh)
                                                                    a500)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____3568
                                                                    =
                                                                    let uu____3571
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "ngoals"
                                                                    (fun a501
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals)
                                                                    a501)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____3572
                                                                    =
                                                                    let uu____3575
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "ngoals_smt"
                                                                    (fun a502
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals_smt)
                                                                    a502)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____3576
                                                                    =
                                                                    let uu____3579
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "is_guard"
                                                                    (fun a503
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    a503)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____3580
                                                                    =
                                                                    let uu____3583
                                                                    =
                                                                    let uu____3584
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Embeddings.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "uvar_env"
                                                                    (fun a504
                                                                     ->
                                                                    fun a505 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a504 a505)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    uu____3584)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____3593
                                                                    =
                                                                    let uu____3596
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "unify"
                                                                    (fun a506
                                                                     ->
                                                                    fun a507 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a506 a507)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____3597
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "launch_process"
                                                                    (fun a508
                                                                     ->
                                                                    fun a509 
                                                                    ->
                                                                    fun a510 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a508 a509
                                                                    a510)
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
                                                                    let uu____3601
                                                                    =
                                                                    let uu____3604
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "fresh_bv_named"
                                                                    (fun a511
                                                                     ->
                                                                    fun a512 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_bv_named)
                                                                    a511 a512)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_bv)
                                                                    FStar_Syntax_Syntax.t_bv
                                                                     in
                                                                    let uu____3605
                                                                    =
                                                                    let uu____3608
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "change"
                                                                    (fun a513
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.change)
                                                                    a513)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____3609
                                                                    =
                                                                    let uu____3612
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "get_guard_policy"
                                                                    (fun a514
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.get_guard_policy)
                                                                    a514)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.embed_guard_policy)
                                                                    FStar_Tactics_Embedding.t_guard_policy
                                                                     in
                                                                    let uu____3613
                                                                    =
                                                                    let uu____3616
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "set_guard_policy"
                                                                    (fun a515
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.set_guard_policy)
                                                                    a515)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    [uu____3616;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____3612
                                                                    ::
                                                                    uu____3613
                                                                     in
                                                                    uu____3608
                                                                    ::
                                                                    uu____3609
                                                                     in
                                                                    uu____3604
                                                                    ::
                                                                    uu____3605
                                                                     in
                                                                    uu____3600
                                                                    ::
                                                                    uu____3601
                                                                     in
                                                                    uu____3596
                                                                    ::
                                                                    uu____3597
                                                                     in
                                                                    uu____3583
                                                                    ::
                                                                    uu____3593
                                                                     in
                                                                    uu____3579
                                                                    ::
                                                                    uu____3580
                                                                     in
                                                                    uu____3575
                                                                    ::
                                                                    uu____3576
                                                                     in
                                                                    uu____3571
                                                                    ::
                                                                    uu____3572
                                                                     in
                                                                    uu____3567
                                                                    ::
                                                                    uu____3568
                                                                     in
                                                                    uu____3563
                                                                    ::
                                                                    uu____3564
                                                                     in
                                                                    uu____3559
                                                                    ::
                                                                    uu____3560
                                                                     in
                                                                    uu____3555
                                                                    ::
                                                                    uu____3556
                                                                     in
                                                                    uu____3551
                                                                    ::
                                                                    uu____3552
                                                                     in
                                                                    uu____3547
                                                                    ::
                                                                    uu____3548
                                                                     in
                                                                    uu____3543
                                                                    ::
                                                                    uu____3544
                                                                     in
                                                                    uu____3525
                                                                    ::
                                                                    uu____3540
                                                                     in
                                                                    uu____3521
                                                                    ::
                                                                    uu____3522
                                                                     in
                                                                    uu____3517
                                                                    ::
                                                                    uu____3518
                                                                     in
                                                                    uu____3513
                                                                    ::
                                                                    uu____3514
                                                                     in
                                                                    uu____3509
                                                                    ::
                                                                    uu____3510
                                                                     in
                                                                    uu____3505
                                                                    ::
                                                                    uu____3506
                                                                     in
                                                                    uu____3501
                                                                    ::
                                                                    uu____3502
                                                                     in
                                                                    uu____3497
                                                                    ::
                                                                    uu____3498
                                                                     in
                                                                    uu____3463
                                                                    ::
                                                                    uu____3494
                                                                     in
                                                                    uu____3459
                                                                    ::
                                                                    uu____3460
                                                                     in
                                                                  uu____3455
                                                                    ::
                                                                    uu____3456
                                                                   in
                                                                uu____3451 ::
                                                                  uu____3452
                                                                 in
                                                              uu____3447 ::
                                                                uu____3448
                                                               in
                                                            uu____3443 ::
                                                              uu____3444
                                                             in
                                                          uu____3439 ::
                                                            uu____3440
                                                           in
                                                        uu____3435 ::
                                                          uu____3436
                                                         in
                                                      uu____3431 ::
                                                        uu____3432
                                                       in
                                                    uu____3427 :: uu____3428
                                                     in
                                                  uu____3423 :: uu____3424
                                                   in
                                                uu____3419 :: uu____3420  in
                                              uu____3398 :: uu____3416  in
                                            uu____3394 :: uu____3395  in
                                          uu____3390 :: uu____3391  in
                                        uu____3386 :: uu____3387  in
                                      uu____3382 :: uu____3383  in
                                    uu____3378 :: uu____3379  in
                                  uu____3374 :: uu____3375  in
                                uu____3370 :: uu____3371  in
                              uu____3366 :: uu____3367  in
                            uu____3362 :: uu____3363  in
                          uu____3358 :: uu____3359  in
                        uu____3354 :: uu____3355  in
                      uu____3350 :: uu____3351  in
                    uu____3337 :: uu____3347  in
                  uu____3324 :: uu____3334  in
                uu____3311 :: uu____3321  in
              uu____3293 :: uu____3308  in
            uu____3289 :: uu____3290  in
          uu____3272 :: uu____3286  in
        uu____3268 :: uu____3269  in
      uu____3262 :: uu____3265  in
    FStar_List.append uu____3259
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
               let uu____3646 =
                 let uu____3647 =
                   let uu____3648 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____3648]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____3647  in
               uu____3646 FStar_Pervasives_Native.None rng  in
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
             let uu____3677 =
               let uu____3678 =
                 let uu____3679 =
                   let uu____3680 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____3680  in
                 [uu____3679]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3678  in
             uu____3677 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____3687 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____3687
            then
              let uu____3688 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____3688
            else ());
           (let result =
              let uu____3691 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____3691 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____3695 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____3695
             then
               let uu____3696 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____3696
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____3741 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3741
                   (fun uu____3745  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____3768 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3768
                   (fun uu____3772  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____3785 =
                   let uu____3790 =
                     let uu____3791 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____3791
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____3790)  in
                 FStar_Errors.raise_error uu____3785
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____3800 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
        uu____3800

let unembed_tactic_1_alt :
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
               let uu____3879 =
                 let uu____3880 =
                   let uu____3881 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____3881]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____3880  in
               uu____3879 FStar_Pervasives_Native.None rng  in
             let app1 = FStar_Syntax_Util.mk_reify app  in
             unembed_tactic_0 res app1)
  
let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____3932  ->
             match uu____3932 with
             | (r,uu____3952,uv,uu____3954,ty,rng) ->
                 let uu____3957 =
                   let uu____3958 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____3959 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____3958 uu____3959 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____3957, rng)) is
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
        (let uu____4008 = FStar_ST.op_Bang tacdbg  in
         if uu____4008
         then
           let uu____4028 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____4028
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____4032 = FStar_ST.op_Bang tacdbg  in
          if uu____4032
          then
            let uu____4052 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____4052
          else ());
         (let uu____4054 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____4054 with
          | (uu____4067,uu____4068,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic1
                   in
                let uu____4075 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____4075 with
                | (env1,uu____4089) ->
                    let env2 =
                      let uu___59_4095 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___59_4095.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___59_4095.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___59_4095.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___59_4095.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___59_4095.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___59_4095.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___59_4095.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___59_4095.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___59_4095.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___59_4095.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___59_4095.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___59_4095.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___59_4095.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___59_4095.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___59_4095.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___59_4095.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___59_4095.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___59_4095.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___59_4095.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___59_4095.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___59_4095.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___59_4095.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___59_4095.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___59_4095.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___59_4095.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___59_4095.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___59_4095.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___59_4095.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___59_4095.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___59_4095.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___59_4095.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___59_4095.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___59_4095.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___59_4095.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___59_4095.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let env3 =
                      let uu___60_4097 = env2  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___60_4097.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___60_4097.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___60_4097.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___60_4097.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___60_4097.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___60_4097.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___60_4097.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___60_4097.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___60_4097.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___60_4097.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___60_4097.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___60_4097.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___60_4097.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___60_4097.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___60_4097.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___60_4097.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___60_4097.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___60_4097.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___60_4097.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes = true;
                        FStar_TypeChecker_Env.failhard =
                          (uu___60_4097.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___60_4097.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___60_4097.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___60_4097.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___60_4097.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___60_4097.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___60_4097.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___60_4097.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___60_4097.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___60_4097.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___60_4097.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___60_4097.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___60_4097.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___60_4097.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___60_4097.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___60_4097.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____4098 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ  in
                    (match uu____4098 with
                     | (ps,w) ->
                         ((let uu____4112 = FStar_ST.op_Bang tacdbg  in
                           if uu____4112
                           then
                             let uu____4132 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____4132
                           else ());
                          (let uu____4134 =
                             FStar_Util.record_time
                               (fun uu____4144  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____4134 with
                           | (res,ms) ->
                               ((let uu____4158 = FStar_ST.op_Bang tacdbg  in
                                 if uu____4158
                                 then
                                   let uu____4178 =
                                     FStar_Syntax_Print.term_to_string
                                       tactic1
                                      in
                                   let uu____4179 =
                                     FStar_Util.string_of_int ms  in
                                   let uu____4180 =
                                     FStar_Syntax_Print.lid_to_string
                                       env3.FStar_TypeChecker_Env.curmodule
                                      in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____4178 uu____4179 uu____4180
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____4188,ps1) ->
                                     ((let uu____4191 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____4191
                                       then
                                         let uu____4211 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____4211
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____4218 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____4218
                                           then
                                             let uu____4219 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____4219
                                              then ()
                                              else
                                                (let uu____4221 =
                                                   let uu____4222 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____4222
                                                    in
                                                 failwith uu____4221))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___61_4225 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___61_4225.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___61_4225.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___61_4225.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____4227 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env3 g1
                                            in
                                         FStar_All.pipe_right uu____4227
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____4234 =
                                         let uu____4235 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____4235 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____4234 "at the time of failure");
                                      (let uu____4236 =
                                         let uu____4241 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____4241)
                                          in
                                       FStar_Errors.raise_error uu____4236
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____4251 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____4255 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____4259 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____4308 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____4344 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____4394 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____4432 . 'Auu____4432 -> 'Auu____4432 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____4451 = FStar_Syntax_Util.head_and_args t  in
        match uu____4451 with
        | (hd1,args) ->
            let uu____4488 =
              let uu____4501 =
                let uu____4502 = FStar_Syntax_Util.un_uinst hd1  in
                uu____4502.FStar_Syntax_Syntax.n  in
              (uu____4501, args)  in
            (match uu____4488 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____4515))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____4578 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____4578 with
                       | (gs,uu____4586) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____4593 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____4593 with
                       | (gs,uu____4601) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____4652 =
                        let uu____4659 =
                          let uu____4662 =
                            let uu____4663 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____4663
                             in
                          [uu____4662]  in
                        (FStar_Syntax_Util.t_true, uu____4659)  in
                      Simplified uu____4652
                  | Both  ->
                      let uu____4674 =
                        let uu____4687 =
                          let uu____4690 =
                            let uu____4691 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____4691
                             in
                          [uu____4690]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____4687)  in
                      Dual uu____4674
                  | Neg  -> Simplified (assertion, []))
             | uu____4712 -> Unchanged t)
  
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
    fun uu___57_4792  ->
      match uu___57_4792 with
      | Unchanged t -> let uu____4798 = f t  in Unchanged uu____4798
      | Simplified (t,gs) ->
          let uu____4805 = let uu____4812 = f t  in (uu____4812, gs)  in
          Simplified uu____4805
      | Dual (tn,tp,gs) ->
          let uu____4822 =
            let uu____4831 = f tn  in
            let uu____4832 = f tp  in (uu____4831, uu____4832, gs)  in
          Dual uu____4822
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____4886 = f t1 t2  in Unchanged uu____4886
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____4898 = let uu____4905 = f t1 t2  in (uu____4905, gs)
               in
            Simplified uu____4898
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____4919 = let uu____4926 = f t1 t2  in (uu____4926, gs)
               in
            Simplified uu____4919
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____4945 =
              let uu____4952 = f t1 t2  in
              (uu____4952, (FStar_List.append gs1 gs2))  in
            Simplified uu____4945
        | uu____4955 ->
            let uu____4964 = explode x  in
            (match uu____4964 with
             | (n1,p1,gs1) ->
                 let uu____4982 = explode y  in
                 (match uu____4982 with
                  | (n2,p2,gs2) ->
                      let uu____5000 =
                        let uu____5009 = f n1 n2  in
                        let uu____5010 = f p1 p2  in
                        (uu____5009, uu____5010, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____5000))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____5075 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____5075
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____5118  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____5152 =
              let uu____5153 = FStar_Syntax_Subst.compress t  in
              uu____5153.FStar_Syntax_Syntax.n  in
            match uu____5152 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____5165 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____5165 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____5189 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____5189 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____5207;
                   FStar_Syntax_Syntax.vars = uu____5208;_},(p,uu____5210)::
                 (q,uu____5212)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____5252 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5252
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____5255 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____5255 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____5261 = FStar_Syntax_Util.mk_imp l r  in
                       uu____5261.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____5265;
                   FStar_Syntax_Syntax.vars = uu____5266;_},(p,uu____5268)::
                 (q,uu____5270)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____5310 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5310
                   in
                let xq =
                  let uu____5312 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5312
                   in
                let r1 =
                  let uu____5314 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____5314 p  in
                let r2 =
                  let uu____5316 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____5316 q  in
                (match (r1, r2) with
                 | (Unchanged uu____5319,Unchanged uu____5320) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____5330 = FStar_Syntax_Util.mk_iff l r  in
                            uu____5330.FStar_Syntax_Syntax.n) r1 r2
                 | uu____5333 ->
                     let uu____5338 = explode r1  in
                     (match uu____5338 with
                      | (pn,pp,gs1) ->
                          let uu____5356 = explode r2  in
                          (match uu____5356 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____5377 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____5378 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____5377
                                   uu____5378
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____5430  ->
                       fun r  ->
                         match uu____5430 with
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
                let uu____5548 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____5548 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____5582  ->
                            match uu____5582 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____5596 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___62_5620 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___62_5620.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___62_5620.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____5596 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____5640 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____5640.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____5686 = traverse f pol e t1  in
                let uu____5691 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____5691 uu____5686
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___63_5729 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___63_5729.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___63_5729.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____5736 =
                f pol e
                  (let uu___64_5740 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___64_5740.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___64_5740.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____5736
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___65_5750 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___65_5750.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___65_5750.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____5751 = explode rp  in
              (match uu____5751 with
               | (uu____5760,p',gs') ->
                   Dual
                     ((let uu___66_5774 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___66_5774.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___66_5774.FStar_Syntax_Syntax.vars)
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
      (let uu____5809 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5809);
      (let uu____5830 = FStar_ST.op_Bang tacdbg  in
       if uu____5830
       then
         let uu____5850 =
           let uu____5851 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____5851
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____5852 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____5850
           uu____5852
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____5881 =
         let uu____5888 = traverse by_tactic_interp Pos env goal  in
         match uu____5888 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____5906 -> failwith "no"  in
       match uu____5881 with
       | (t',gs) ->
           ((let uu____5928 = FStar_ST.op_Bang tacdbg  in
             if uu____5928
             then
               let uu____5948 =
                 let uu____5949 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____5949
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____5950 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____5948 uu____5950
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5997  ->
                    fun g  ->
                      match uu____5997 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____6042 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____6042 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____6045 =
                                  let uu____6050 =
                                    let uu____6051 =
                                      FStar_Syntax_Print.term_to_string
                                        g.FStar_Tactics_Types.goal_ty
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____6051
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____6050)
                                   in
                                FStar_Errors.raise_error uu____6045
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____6054 = FStar_ST.op_Bang tacdbg  in
                            if uu____6054
                            then
                              let uu____6074 = FStar_Util.string_of_int n1
                                 in
                              let uu____6075 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____6074 uu____6075
                            else ());
                           (let gt' =
                              let uu____6078 =
                                let uu____6079 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____6079
                                 in
                              FStar_TypeChecker_Util.label uu____6078
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____6094 = s1  in
             match uu____6094 with
             | (uu____6115,gs1) ->
                 let uu____6133 =
                   let uu____6140 = FStar_Options.peek ()  in
                   (env, t', uu____6140)  in
                 uu____6133 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____6151 =
        let uu____6152 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____6152  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____6151 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____6153 =
      let uu____6154 =
        let uu____6155 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____6156 =
          let uu____6159 = FStar_Syntax_Syntax.as_arg a  in [uu____6159]  in
        uu____6155 :: uu____6156  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____6154  in
    uu____6153 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____6172 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____6172);
        (let uu____6192 =
           let uu____6199 = reify_tactic tau  in
           run_tactic_on_typ uu____6199 env typ  in
         match uu____6192 with
         | (gs,w) ->
             let uu____6206 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____6210 =
                      let uu____6211 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____6211  in
                    Prims.op_Negation uu____6210) gs
                in
             if uu____6206
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
      (let uu____6226 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____6226);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____6247 =
         let uu____6254 = reify_tactic tau  in
         run_tactic_on_typ uu____6254 env typ  in
       match uu____6247 with
       | (gs,w) ->
           ((let uu____6264 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____6268 =
                      let uu____6269 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____6269  in
                    Prims.op_Negation uu____6268) gs
                in
             if uu____6264
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
             let uu____6274 =
               let uu____6279 =
                 FStar_Syntax_Embeddings.unembed_list
                   FStar_Reflection_Embeddings.unembed_sigelt
                  in
               uu____6279 w1  in
             FStar_All.pipe_left FStar_Util.must uu____6274)))
  