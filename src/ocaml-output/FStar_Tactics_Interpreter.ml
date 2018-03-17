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
                fun unembed_e1  ->
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
                                                            unembed_e1 e  in
                                                          FStar_Util.bind_opt
                                                            uu____1775
                                                            (fun e1  ->
                                                               let uu____1783
                                                                 =
                                                                 unembed_e1 f
                                                                  in
                                                               FStar_Util.bind_opt
                                                                 uu____1783
                                                                 (fun f1  ->
                                                                    let res =
                                                                    let uu____1795
                                                                    =
                                                                    t a1 b1
                                                                    c1 d1
                                                                    (Obj.magic
                                                                    e1) f1
                                                                     in
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
      | (ps,uu____2391)::[] ->
          let uu____2408 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2408
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2416 =
                 let uu____2417 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2418 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____2417
                   uu____2418
                  in
               FStar_Pervasives_Native.Some uu____2416)
      | uu____2419 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____2423 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2423;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____2436)::[] ->
          let uu____2453 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2453
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2461 =
                 let uu____2462 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2463 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____2462
                   uu____2463
                  in
               FStar_Pervasives_Native.Some uu____2461)
      | uu____2464 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____2468 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2468;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____2485)::[] ->
          let uu____2502 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2502
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2515 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2532)::(r,uu____2534)::[] ->
          let uu____2561 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2561
            (fun ps1  ->
               let uu____2567 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____2567
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2575 =
                      let uu____2576 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____2576 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2575))
      | uu____2577 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____2592)::(b,uu____2594)::[] ->
          let uu____2621 = FStar_Reflection_Embeddings.unembed_env env_t  in
          FStar_Util.bind_opt uu____2621
            (fun env  ->
               let uu____2627 = FStar_Reflection_Embeddings.unembed_binder b
                  in
               FStar_Util.bind_opt uu____2627
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____2635 =
                      FStar_Reflection_Embeddings.embed_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____2635))
      | uu____2636 -> failwith "Unexpected application of push_binder"  in
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
      let uu___58_2652 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___58_2652.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___58_2652.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____2659 =
      let uu____2662 =
        mktac2 () () () "__fail"
          (fun a438  ->
             fun a439  ->
               (Obj.magic (fun uu____2664  -> FStar_Tactics_Basic.fail)) a438
                 a439) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____2665 =
        let uu____2668 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____2669 =
          let uu____2672 =
            let uu____2673 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a440  ->
                 fun a441  ->
                   (Obj.magic (fun uu____2679  -> FStar_Tactics_Basic.trytac))
                     a440 a441) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____2673)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2686 =
            let uu____2689 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Embeddings.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____2690 =
              let uu____2693 =
                let uu____2694 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____2701 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____2694) uu____2701
                 in
              let uu____2708 =
                let uu____2711 =
                  let uu____2712 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "__norm"
                    (fun a442  -> (Obj.magic FStar_Tactics_Basic.norm) a442)
                    (Obj.magic uu____2712)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____2721 =
                  let uu____2724 =
                    let uu____2725 =
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
                      (Obj.magic uu____2725)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_term)
                      (Obj.magic FStar_Reflection_Embeddings.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2734 =
                    let uu____2737 =
                      let uu____2738 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "__norm_binder_type"
                        (fun a446  ->
                           fun a447  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a446 a447) (Obj.magic uu____2738)
                        (Obj.magic FStar_Reflection_Embeddings.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2747 =
                      let uu____2750 =
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
                      let uu____2751 =
                        let uu____2754 =
                          mktac1 () () "__binder_retype"
                            (fun a450  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a450)
                            (Obj.magic
                               FStar_Reflection_Embeddings.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2755 =
                          let uu____2758 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2759 =
                            let uu____2762 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2763 =
                              let uu____2766 =
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
                              let uu____2767 =
                                let uu____2770 =
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
                                let uu____2771 =
                                  let uu____2774 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2775 =
                                    let uu____2778 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2779 =
                                      let uu____2782 =
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
                                      let uu____2783 =
                                        let uu____2786 =
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
                                        let uu____2787 =
                                          let uu____2790 =
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
                                          let uu____2791 =
                                            let uu____2794 =
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
                                            let uu____2795 =
                                              let uu____2798 =
                                                let uu____2799 =
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
                                                                   uu____2808
                                                                    ->
                                                                   fun
                                                                    uu____2809
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
                                                  (Obj.magic uu____2799)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2816 =
                                                let uu____2819 =
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
                                                let uu____2820 =
                                                  let uu____2823 =
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
                                                  let uu____2824 =
                                                    let uu____2827 =
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
                                                    let uu____2828 =
                                                      let uu____2831 =
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
                                                      let uu____2832 =
                                                        let uu____2835 =
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
                                                        let uu____2836 =
                                                          let uu____2839 =
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
                                                          let uu____2840 =
                                                            let uu____2843 =
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
                                                            let uu____2844 =
                                                              let uu____2847
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
                                                              let uu____2852
                                                                =
                                                                let uu____2855
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
                                                                let uu____2856
                                                                  =
                                                                  let uu____2859
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
                                                                  let uu____2860
                                                                    =
                                                                    let uu____2863
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
                                                                    let uu____2864
                                                                    =
                                                                    let uu____2867
                                                                    =
                                                                    let uu____2868
                                                                    =
                                                                    let uu____2879
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_pair
                                                                    FStar_Syntax_Embeddings.unembed_bool
                                                                    FStar_Syntax_Embeddings.unembed_int
                                                                     in
                                                                    unembed_tactic_1
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    uu____2879
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
                                                                    uu____2868)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2898
                                                                    =
                                                                    let uu____2901
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2902
                                                                    =
                                                                    let uu____2905
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2906
                                                                    =
                                                                    let uu____2909
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2910
                                                                    =
                                                                    let uu____2913
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2914
                                                                    =
                                                                    let uu____2917
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2918
                                                                    =
                                                                    let uu____2921
                                                                    =
                                                                    mktac0 ()
                                                                    "__dismiss"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dismiss)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2922
                                                                    =
                                                                    let uu____2925
                                                                    =
                                                                    mktac0 ()
                                                                    "__tadmit"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.tadmit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2926
                                                                    =
                                                                    let uu____2929
                                                                    =
                                                                    let uu____2930
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2937
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
                                                                    uu____2930)
                                                                    uu____2937
                                                                     in
                                                                    let uu____2944
                                                                    =
                                                                    let uu____2947
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2948
                                                                    =
                                                                    let uu____2951
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2952
                                                                    =
                                                                    let uu____2955
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2956
                                                                    =
                                                                    let uu____2959
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2960
                                                                    =
                                                                    let uu____2963
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
                                                                    let uu____2964
                                                                    =
                                                                    let uu____2967
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
                                                                    let uu____2968
                                                                    =
                                                                    let uu____2971
                                                                    =
                                                                    mktac0 ()
                                                                    "__fresh"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2972
                                                                    =
                                                                    let uu____2975
                                                                    =
                                                                    mktac0 ()
                                                                    "__ngoals"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2976
                                                                    =
                                                                    let uu____2979
                                                                    =
                                                                    mktac0 ()
                                                                    "__ngoals_smt"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals_smt)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2980
                                                                    =
                                                                    let uu____2983
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2984
                                                                    =
                                                                    let uu____2987
                                                                    =
                                                                    let uu____2988
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
                                                                    uu____2988)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2997
                                                                    =
                                                                    let uu____3000
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
                                                                    let uu____3001
                                                                    =
                                                                    let uu____3004
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
                                                                    let uu____3005
                                                                    =
                                                                    let uu____3008
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
                                                                    let uu____3009
                                                                    =
                                                                    let uu____3012
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
                                                                    let uu____3013
                                                                    =
                                                                    let uu____3016
                                                                    =
                                                                    mktac0 ()
                                                                    "__get_guard_policy"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.get_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.embed_guard_policy)
                                                                    FStar_Tactics_Embedding.t_guard_policy
                                                                     in
                                                                    let uu____3017
                                                                    =
                                                                    let uu____3020
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
                                                                    [uu____3020;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____3016
                                                                    ::
                                                                    uu____3017
                                                                     in
                                                                    uu____3012
                                                                    ::
                                                                    uu____3013
                                                                     in
                                                                    uu____3008
                                                                    ::
                                                                    uu____3009
                                                                     in
                                                                    uu____3004
                                                                    ::
                                                                    uu____3005
                                                                     in
                                                                    uu____3000
                                                                    ::
                                                                    uu____3001
                                                                     in
                                                                    uu____2987
                                                                    ::
                                                                    uu____2997
                                                                     in
                                                                    uu____2983
                                                                    ::
                                                                    uu____2984
                                                                     in
                                                                    uu____2979
                                                                    ::
                                                                    uu____2980
                                                                     in
                                                                    uu____2975
                                                                    ::
                                                                    uu____2976
                                                                     in
                                                                    uu____2971
                                                                    ::
                                                                    uu____2972
                                                                     in
                                                                    uu____2967
                                                                    ::
                                                                    uu____2968
                                                                     in
                                                                    uu____2963
                                                                    ::
                                                                    uu____2964
                                                                     in
                                                                    uu____2959
                                                                    ::
                                                                    uu____2960
                                                                     in
                                                                    uu____2955
                                                                    ::
                                                                    uu____2956
                                                                     in
                                                                    uu____2951
                                                                    ::
                                                                    uu____2952
                                                                     in
                                                                    uu____2947
                                                                    ::
                                                                    uu____2948
                                                                     in
                                                                    uu____2929
                                                                    ::
                                                                    uu____2944
                                                                     in
                                                                    uu____2925
                                                                    ::
                                                                    uu____2926
                                                                     in
                                                                    uu____2921
                                                                    ::
                                                                    uu____2922
                                                                     in
                                                                    uu____2917
                                                                    ::
                                                                    uu____2918
                                                                     in
                                                                    uu____2913
                                                                    ::
                                                                    uu____2914
                                                                     in
                                                                    uu____2909
                                                                    ::
                                                                    uu____2910
                                                                     in
                                                                    uu____2905
                                                                    ::
                                                                    uu____2906
                                                                     in
                                                                    uu____2901
                                                                    ::
                                                                    uu____2902
                                                                     in
                                                                    uu____2867
                                                                    ::
                                                                    uu____2898
                                                                     in
                                                                    uu____2863
                                                                    ::
                                                                    uu____2864
                                                                     in
                                                                  uu____2859
                                                                    ::
                                                                    uu____2860
                                                                   in
                                                                uu____2855 ::
                                                                  uu____2856
                                                                 in
                                                              uu____2847 ::
                                                                uu____2852
                                                               in
                                                            uu____2843 ::
                                                              uu____2844
                                                             in
                                                          uu____2839 ::
                                                            uu____2840
                                                           in
                                                        uu____2835 ::
                                                          uu____2836
                                                         in
                                                      uu____2831 ::
                                                        uu____2832
                                                       in
                                                    uu____2827 :: uu____2828
                                                     in
                                                  uu____2823 :: uu____2824
                                                   in
                                                uu____2819 :: uu____2820  in
                                              uu____2798 :: uu____2816  in
                                            uu____2794 :: uu____2795  in
                                          uu____2790 :: uu____2791  in
                                        uu____2786 :: uu____2787  in
                                      uu____2782 :: uu____2783  in
                                    uu____2778 :: uu____2779  in
                                  uu____2774 :: uu____2775  in
                                uu____2770 :: uu____2771  in
                              uu____2766 :: uu____2767  in
                            uu____2762 :: uu____2763  in
                          uu____2758 :: uu____2759  in
                        uu____2754 :: uu____2755  in
                      uu____2750 :: uu____2751  in
                    uu____2737 :: uu____2747  in
                  uu____2724 :: uu____2734  in
                uu____2711 :: uu____2721  in
              uu____2693 :: uu____2708  in
            uu____2689 :: uu____2690  in
          uu____2672 :: uu____2686  in
        uu____2668 :: uu____2669  in
      uu____2662 :: uu____2665  in
    FStar_List.append uu____2659
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
               let uu____3050 =
                 let uu____3051 =
                   let uu____3052 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____3052]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____3051  in
               uu____3050 FStar_Pervasives_Native.None rng  in
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
             let uu____3081 =
               let uu____3082 =
                 let uu____3083 =
                   let uu____3084 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____3084  in
                 [uu____3083]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3082  in
             uu____3081 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____3091 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____3091
            then
              let uu____3092 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____3092
            else ());
           (let result =
              let uu____3095 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____3095 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____3099 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____3099
             then
               let uu____3100 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____3100
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____3145 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3145
                   (fun uu____3149  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____3172 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3172
                   (fun uu____3176  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____3189 =
                   let uu____3194 =
                     let uu____3195 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____3195
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____3194)  in
                 FStar_Errors.raise_error uu____3189
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____3204 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
        uu____3204

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____3260  ->
             match uu____3260 with
             | (r,uu____3280,uv,uu____3282,ty,rng) ->
                 let uu____3285 =
                   let uu____3286 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____3287 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____3286 uu____3287 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____3285, rng)) is
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
        (let uu____3336 = FStar_ST.op_Bang tacdbg  in
         if uu____3336
         then
           let uu____3356 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____3356
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____3360 = FStar_ST.op_Bang tacdbg  in
          if uu____3360
          then
            let uu____3380 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____3380
          else ());
         (let uu____3382 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____3382 with
          | (uu____3395,uu____3396,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic1
                   in
                let uu____3403 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____3403 with
                | (env1,uu____3417) ->
                    let env2 =
                      let uu___59_3423 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___59_3423.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___59_3423.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___59_3423.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___59_3423.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___59_3423.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___59_3423.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___59_3423.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___59_3423.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___59_3423.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___59_3423.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___59_3423.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___59_3423.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___59_3423.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___59_3423.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___59_3423.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___59_3423.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___59_3423.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___59_3423.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___59_3423.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___59_3423.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___59_3423.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___59_3423.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___59_3423.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___59_3423.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___59_3423.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___59_3423.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___59_3423.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___59_3423.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___59_3423.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___59_3423.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___59_3423.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___59_3423.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___59_3423.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___59_3423.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___59_3423.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let env3 =
                      let uu___60_3425 = env2  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___60_3425.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___60_3425.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___60_3425.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___60_3425.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___60_3425.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___60_3425.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___60_3425.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___60_3425.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___60_3425.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___60_3425.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___60_3425.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___60_3425.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___60_3425.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___60_3425.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___60_3425.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___60_3425.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___60_3425.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___60_3425.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___60_3425.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes = true;
                        FStar_TypeChecker_Env.failhard =
                          (uu___60_3425.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___60_3425.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___60_3425.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___60_3425.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___60_3425.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___60_3425.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___60_3425.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___60_3425.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___60_3425.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___60_3425.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___60_3425.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___60_3425.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___60_3425.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___60_3425.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___60_3425.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___60_3425.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____3426 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ  in
                    (match uu____3426 with
                     | (ps,w) ->
                         ((let uu____3440 = FStar_ST.op_Bang tacdbg  in
                           if uu____3440
                           then
                             let uu____3460 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____3460
                           else ());
                          (let uu____3462 =
                             FStar_Util.record_time
                               (fun uu____3472  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____3462 with
                           | (res,ms) ->
                               ((let uu____3486 = FStar_ST.op_Bang tacdbg  in
                                 if uu____3486
                                 then
                                   let uu____3506 =
                                     FStar_Syntax_Print.term_to_string
                                       tactic1
                                      in
                                   let uu____3507 =
                                     FStar_Util.string_of_int ms  in
                                   let uu____3508 =
                                     FStar_Syntax_Print.lid_to_string
                                       env3.FStar_TypeChecker_Env.curmodule
                                      in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____3506 uu____3507 uu____3508
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____3516,ps1) ->
                                     ((let uu____3519 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____3519
                                       then
                                         let uu____3539 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____3539
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____3546 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____3546
                                           then
                                             let uu____3547 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____3547
                                              then ()
                                              else
                                                (let uu____3549 =
                                                   let uu____3550 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____3550
                                                    in
                                                 failwith uu____3549))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___61_3553 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___61_3553.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___61_3553.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___61_3553.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____3555 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env3 g1
                                            in
                                         FStar_All.pipe_right uu____3555
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____3562 =
                                         let uu____3563 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____3563 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____3562 "at the time of failure");
                                      (let uu____3564 =
                                         let uu____3569 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____3569)
                                          in
                                       FStar_Errors.raise_error uu____3564
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____3579 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____3583 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____3587 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3636 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3672 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3722 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3760 . 'Auu____3760 -> 'Auu____3760 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3779 = FStar_Syntax_Util.head_and_args t  in
        match uu____3779 with
        | (hd1,args) ->
            let uu____3816 =
              let uu____3829 =
                let uu____3830 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3830.FStar_Syntax_Syntax.n  in
              (uu____3829, args)  in
            (match uu____3816 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3843))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3906 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3906 with
                       | (gs,uu____3914) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3921 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3921 with
                       | (gs,uu____3929) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3980 =
                        let uu____3987 =
                          let uu____3990 =
                            let uu____3991 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3991
                             in
                          [uu____3990]  in
                        (FStar_Syntax_Util.t_true, uu____3987)  in
                      Simplified uu____3980
                  | Both  ->
                      let uu____4002 =
                        let uu____4015 =
                          let uu____4018 =
                            let uu____4019 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____4019
                             in
                          [uu____4018]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____4015)  in
                      Dual uu____4002
                  | Neg  -> Simplified (assertion, []))
             | uu____4040 -> Unchanged t)
  
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
    fun uu___57_4120  ->
      match uu___57_4120 with
      | Unchanged t -> let uu____4126 = f t  in Unchanged uu____4126
      | Simplified (t,gs) ->
          let uu____4133 = let uu____4140 = f t  in (uu____4140, gs)  in
          Simplified uu____4133
      | Dual (tn,tp,gs) ->
          let uu____4150 =
            let uu____4159 = f tn  in
            let uu____4160 = f tp  in (uu____4159, uu____4160, gs)  in
          Dual uu____4150
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____4214 = f t1 t2  in Unchanged uu____4214
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____4226 = let uu____4233 = f t1 t2  in (uu____4233, gs)
               in
            Simplified uu____4226
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____4247 = let uu____4254 = f t1 t2  in (uu____4254, gs)
               in
            Simplified uu____4247
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____4273 =
              let uu____4280 = f t1 t2  in
              (uu____4280, (FStar_List.append gs1 gs2))  in
            Simplified uu____4273
        | uu____4283 ->
            let uu____4292 = explode x  in
            (match uu____4292 with
             | (n1,p1,gs1) ->
                 let uu____4310 = explode y  in
                 (match uu____4310 with
                  | (n2,p2,gs2) ->
                      let uu____4328 =
                        let uu____4337 = f n1 n2  in
                        let uu____4338 = f p1 p2  in
                        (uu____4337, uu____4338, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____4328))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____4403 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____4403
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____4446  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____4480 =
              let uu____4481 = FStar_Syntax_Subst.compress t  in
              uu____4481.FStar_Syntax_Syntax.n  in
            match uu____4480 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____4493 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____4493 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____4517 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____4517 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4535;
                   FStar_Syntax_Syntax.vars = uu____4536;_},(p,uu____4538)::
                 (q,uu____4540)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____4580 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4580
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____4583 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____4583 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4589 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4589.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4593;
                   FStar_Syntax_Syntax.vars = uu____4594;_},(p,uu____4596)::
                 (q,uu____4598)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4638 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4638
                   in
                let xq =
                  let uu____4640 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4640
                   in
                let r1 =
                  let uu____4642 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4642 p  in
                let r2 =
                  let uu____4644 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4644 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4647,Unchanged uu____4648) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4658 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4658.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4661 ->
                     let uu____4666 = explode r1  in
                     (match uu____4666 with
                      | (pn,pp,gs1) ->
                          let uu____4684 = explode r2  in
                          (match uu____4684 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4705 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4706 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4705
                                   uu____4706
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4758  ->
                       fun r  ->
                         match uu____4758 with
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
                let uu____4876 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4876 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4910  ->
                            match uu____4910 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4924 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___62_4948 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___62_4948.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___62_4948.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4924 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4968 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4968.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____5014 = traverse f pol e t1  in
                let uu____5019 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____5019 uu____5014
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___63_5057 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___63_5057.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___63_5057.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____5064 =
                f pol e
                  (let uu___64_5068 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___64_5068.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___64_5068.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____5064
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___65_5078 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___65_5078.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___65_5078.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____5079 = explode rp  in
              (match uu____5079 with
               | (uu____5088,p',gs') ->
                   Dual
                     ((let uu___66_5102 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___66_5102.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___66_5102.FStar_Syntax_Syntax.vars)
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
      (let uu____5137 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5137);
      (let uu____5158 = FStar_ST.op_Bang tacdbg  in
       if uu____5158
       then
         let uu____5178 =
           let uu____5179 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____5179
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____5180 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____5178
           uu____5180
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____5209 =
         let uu____5216 = traverse by_tactic_interp Pos env goal  in
         match uu____5216 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____5234 -> failwith "no"  in
       match uu____5209 with
       | (t',gs) ->
           ((let uu____5256 = FStar_ST.op_Bang tacdbg  in
             if uu____5256
             then
               let uu____5276 =
                 let uu____5277 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____5277
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____5278 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____5276 uu____5278
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5325  ->
                    fun g  ->
                      match uu____5325 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5370 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____5370 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5373 =
                                  let uu____5378 =
                                    let uu____5379 =
                                      FStar_Syntax_Print.term_to_string
                                        g.FStar_Tactics_Types.goal_ty
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5379
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5378)
                                   in
                                FStar_Errors.raise_error uu____5373
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5382 = FStar_ST.op_Bang tacdbg  in
                            if uu____5382
                            then
                              let uu____5402 = FStar_Util.string_of_int n1
                                 in
                              let uu____5403 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5402 uu____5403
                            else ());
                           (let gt' =
                              let uu____5406 =
                                let uu____5407 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____5407
                                 in
                              FStar_TypeChecker_Util.label uu____5406
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____5422 = s1  in
             match uu____5422 with
             | (uu____5443,gs1) ->
                 let uu____5461 =
                   let uu____5468 = FStar_Options.peek ()  in
                   (env, t', uu____5468)  in
                 uu____5461 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____5479 =
        let uu____5480 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____5480  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____5479 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____5481 =
      let uu____5482 =
        let uu____5483 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____5484 =
          let uu____5487 = FStar_Syntax_Syntax.as_arg a  in [uu____5487]  in
        uu____5483 :: uu____5484  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____5482  in
    uu____5481 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____5500 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____5500);
        (let uu____5520 =
           let uu____5527 = reify_tactic tau  in
           run_tactic_on_typ uu____5527 env typ  in
         match uu____5520 with
         | (gs,w) ->
             let uu____5534 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5538 =
                      let uu____5539 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5539  in
                    Prims.op_Negation uu____5538) gs
                in
             if uu____5534
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
      (let uu____5554 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5554);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____5575 =
         let uu____5582 = reify_tactic tau  in
         run_tactic_on_typ uu____5582 env typ  in
       match uu____5575 with
       | (gs,w) ->
           ((let uu____5592 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5596 =
                      let uu____5597 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5597  in
                    Prims.op_Negation uu____5596) gs
                in
             if uu____5592
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
             let uu____5602 =
               let uu____5607 =
                 FStar_Syntax_Embeddings.unembed_list
                   FStar_Reflection_Embeddings.unembed_sigelt
                  in
               uu____5607 w1  in
             FStar_All.pipe_left FStar_Util.must uu____5602)))
  