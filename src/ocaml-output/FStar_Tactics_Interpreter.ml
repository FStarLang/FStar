open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mk_tactic_interpretation_0 :
  'r .
    Prims.bool ->
      'r FStar_Tactics_Basic.tac ->
        'r FStar_Syntax_Embeddings.embedding ->
          FStar_Ident.lid ->
            FStar_TypeChecker_Normalize.psc ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun er  ->
        fun nm  ->
          fun psc  ->
            fun args  ->
              match args with
              | (embedded_state,uu____70)::[] ->
                  let uu____87 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Tactics_Embedding.e_proofstate embedded_state
                     in
                  FStar_Util.bind_opt uu____87
                    (fun ps  ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let uu____96 =
                         FStar_Tactics_Basic.log ps1
                           (fun uu____100  ->
                              let uu____101 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____102 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.print2 "Reached %s, args are: %s\n"
                                uu____101 uu____102)
                          in
                       let res =
                         let uu____104 = FStar_Tactics_Embedding.e_result er
                            in
                         let uu____109 =
                           FStar_TypeChecker_Normalize.psc_range psc  in
                         let uu____110 = FStar_Tactics_Basic.run t ps1  in
                         FStar_Syntax_Embeddings.embed uu____104 uu____109
                           uu____110
                          in
                       FStar_Pervasives_Native.Some res)
              | uu____115 ->
                  failwith "Unexpected application of tactic primitive"
  
let mk_tactic_interpretation_1 :
  'a 'r .
    Prims.bool ->
      ('a -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun er  ->
          fun nm  ->
            fun psc  ->
              fun args  ->
                match args with
                | (a,uu____193)::(embedded_state,uu____195)::[] ->
                    let uu____222 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state
                       in
                    FStar_Util.bind_opt uu____222
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let uu____231 =
                           FStar_Tactics_Basic.log ps1
                             (fun uu____235  ->
                                let uu____236 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____237 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____236
                                  uu____237)
                            in
                         let uu____238 = FStar_Syntax_Embeddings.unembed ea a
                            in
                         FStar_Util.bind_opt uu____238
                           (fun a1  ->
                              let res =
                                let uu____248 = t a1  in
                                FStar_Tactics_Basic.run uu____248 ps1  in
                              let uu____251 =
                                let uu____252 =
                                  FStar_Tactics_Embedding.e_result er  in
                                let uu____257 =
                                  FStar_TypeChecker_Normalize.psc_range psc
                                   in
                                FStar_Syntax_Embeddings.embed uu____252
                                  uu____257 res
                                 in
                              FStar_Pervasives_Native.Some uu____251))
                | uu____260 ->
                    let uu____261 =
                      let uu____262 = FStar_Ident.string_of_lid nm  in
                      let uu____263 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____262 uu____263
                       in
                    failwith uu____261
  
let mk_tactic_interpretation_1_env :
  'a 'r .
    Prims.bool ->
      (FStar_TypeChecker_Normalize.psc -> 'a -> 'r FStar_Tactics_Basic.tac)
        ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun er  ->
          fun nm  ->
            fun psc  ->
              fun args  ->
                match args with
                | (a,uu____346)::(embedded_state,uu____348)::[] ->
                    let uu____375 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state
                       in
                    FStar_Util.bind_opt uu____375
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let uu____384 =
                           FStar_Tactics_Basic.log ps1
                             (fun uu____388  ->
                                let uu____389 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____390 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____389
                                  uu____390)
                            in
                         let uu____391 = FStar_Syntax_Embeddings.unembed ea a
                            in
                         FStar_Util.bind_opt uu____391
                           (fun a1  ->
                              let res =
                                let uu____401 = t psc a1  in
                                FStar_Tactics_Basic.run uu____401 ps1  in
                              let uu____404 =
                                let uu____405 =
                                  FStar_Tactics_Embedding.e_result er  in
                                let uu____410 =
                                  FStar_TypeChecker_Normalize.psc_range psc
                                   in
                                FStar_Syntax_Embeddings.embed uu____405
                                  uu____410 res
                                 in
                              FStar_Pervasives_Native.Some uu____404))
                | uu____413 ->
                    let uu____414 =
                      let uu____415 = FStar_Ident.string_of_lid nm  in
                      let uu____416 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____415 uu____416
                       in
                    failwith uu____414
  
let mk_tactic_interpretation_2 :
  'a 'b 'r .
    Prims.bool ->
      ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun nm  ->
              fun psc  ->
                fun args  ->
                  match args with
                  | (a,uu____513)::(b,uu____515)::(embedded_state,uu____517)::[]
                      ->
                      let uu____554 =
                        FStar_Syntax_Embeddings.unembed
                          FStar_Tactics_Embedding.e_proofstate embedded_state
                         in
                      FStar_Util.bind_opt uu____554
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let uu____563 =
                             FStar_Tactics_Basic.log ps1
                               (fun uu____567  ->
                                  let uu____568 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____569 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____568
                                    uu____569)
                              in
                           let uu____570 =
                             FStar_Syntax_Embeddings.unembed ea a  in
                           FStar_Util.bind_opt uu____570
                             (fun a1  ->
                                let uu____576 =
                                  FStar_Syntax_Embeddings.unembed eb b  in
                                FStar_Util.bind_opt uu____576
                                  (fun b1  ->
                                     let res =
                                       let uu____586 = t a1 b1  in
                                       FStar_Tactics_Basic.run uu____586 ps1
                                        in
                                     let uu____589 =
                                       let uu____590 =
                                         FStar_Tactics_Embedding.e_result er
                                          in
                                       let uu____595 =
                                         FStar_TypeChecker_Normalize.psc_range
                                           psc
                                          in
                                       FStar_Syntax_Embeddings.embed
                                         uu____590 uu____595 res
                                        in
                                     FStar_Pervasives_Native.Some uu____589)))
                  | uu____598 ->
                      let uu____599 =
                        let uu____600 = FStar_Ident.string_of_lid nm  in
                        let uu____601 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____600 uu____601
                         in
                      failwith uu____599
  
let mk_tactic_interpretation_3 :
  'a 'b 'c 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'c FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                FStar_Ident.lid ->
                  FStar_TypeChecker_Normalize.psc ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun er  ->
              fun nm  ->
                fun psc  ->
                  fun args  ->
                    match args with
                    | (a,uu____717)::(b,uu____719)::(c,uu____721)::(embedded_state,uu____723)::[]
                        ->
                        let uu____770 =
                          FStar_Syntax_Embeddings.unembed
                            FStar_Tactics_Embedding.e_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____770
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let uu____779 =
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____783  ->
                                    let uu____784 =
                                      FStar_Ident.string_of_lid nm  in
                                    let uu____785 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state
                                       in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n" uu____784
                                      uu____785)
                                in
                             let uu____786 =
                               FStar_Syntax_Embeddings.unembed ea a  in
                             FStar_Util.bind_opt uu____786
                               (fun a1  ->
                                  let uu____792 =
                                    FStar_Syntax_Embeddings.unembed eb b  in
                                  FStar_Util.bind_opt uu____792
                                    (fun b1  ->
                                       let uu____798 =
                                         FStar_Syntax_Embeddings.unembed ec c
                                          in
                                       FStar_Util.bind_opt uu____798
                                         (fun c1  ->
                                            let res =
                                              let uu____808 = t a1 b1 c1  in
                                              FStar_Tactics_Basic.run
                                                uu____808 ps1
                                               in
                                            let uu____811 =
                                              let uu____812 =
                                                FStar_Tactics_Embedding.e_result
                                                  er
                                                 in
                                              let uu____817 =
                                                FStar_TypeChecker_Normalize.psc_range
                                                  psc
                                                 in
                                              FStar_Syntax_Embeddings.embed
                                                uu____812 uu____817 res
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____811))))
                    | uu____820 ->
                        let uu____821 =
                          let uu____822 = FStar_Ident.string_of_lid nm  in
                          let uu____823 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____822 uu____823
                           in
                        failwith uu____821
  
let mk_tactic_interpretation_4 :
  'a 'b 'c 'd 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'd -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'c FStar_Syntax_Embeddings.embedding ->
              'd FStar_Syntax_Embeddings.embedding ->
                'r FStar_Syntax_Embeddings.embedding ->
                  FStar_Ident.lid ->
                    FStar_TypeChecker_Normalize.psc ->
                      FStar_Syntax_Syntax.args ->
                        FStar_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun ed  ->
              fun er  ->
                fun nm  ->
                  fun psc  ->
                    fun args  ->
                      match args with
                      | (a,uu____958)::(b,uu____960)::(c,uu____962)::
                          (d,uu____964)::(embedded_state,uu____966)::[] ->
                          let uu____1023 =
                            FStar_Syntax_Embeddings.unembed
                              FStar_Tactics_Embedding.e_proofstate
                              embedded_state
                             in
                          FStar_Util.bind_opt uu____1023
                            (fun ps  ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let uu____1032 =
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1036  ->
                                      let uu____1037 =
                                        FStar_Ident.string_of_lid nm  in
                                      let uu____1038 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state
                                         in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1037 uu____1038)
                                  in
                               let uu____1039 =
                                 FStar_Syntax_Embeddings.unembed ea a  in
                               FStar_Util.bind_opt uu____1039
                                 (fun a1  ->
                                    let uu____1045 =
                                      FStar_Syntax_Embeddings.unembed eb b
                                       in
                                    FStar_Util.bind_opt uu____1045
                                      (fun b1  ->
                                         let uu____1051 =
                                           FStar_Syntax_Embeddings.unembed ec
                                             c
                                            in
                                         FStar_Util.bind_opt uu____1051
                                           (fun c1  ->
                                              let uu____1057 =
                                                FStar_Syntax_Embeddings.unembed
                                                  ed d
                                                 in
                                              FStar_Util.bind_opt uu____1057
                                                (fun d1  ->
                                                   let res =
                                                     let uu____1067 =
                                                       t a1 b1 c1 d1  in
                                                     FStar_Tactics_Basic.run
                                                       uu____1067 ps1
                                                      in
                                                   let uu____1070 =
                                                     let uu____1071 =
                                                       FStar_Tactics_Embedding.e_result
                                                         er
                                                        in
                                                     let uu____1076 =
                                                       FStar_TypeChecker_Normalize.psc_range
                                                         psc
                                                        in
                                                     FStar_Syntax_Embeddings.embed
                                                       uu____1071 uu____1076
                                                       res
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____1070)))))
                      | uu____1079 ->
                          let uu____1080 =
                            let uu____1081 = FStar_Ident.string_of_lid nm  in
                            let uu____1082 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____1081 uu____1082
                             in
                          failwith uu____1080
  
let mk_tactic_interpretation_5 :
  'a 'b 'c 'd 'e 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'c FStar_Syntax_Embeddings.embedding ->
              'd FStar_Syntax_Embeddings.embedding ->
                'e FStar_Syntax_Embeddings.embedding ->
                  'r FStar_Syntax_Embeddings.embedding ->
                    FStar_Ident.lid ->
                      FStar_TypeChecker_Normalize.psc ->
                        FStar_Syntax_Syntax.args ->
                          FStar_Syntax_Syntax.term
                            FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun ed  ->
              fun ee  ->
                fun er  ->
                  fun nm  ->
                    fun psc  ->
                      fun args  ->
                        match args with
                        | (a,uu____1236)::(b,uu____1238)::(c,uu____1240)::
                            (d,uu____1242)::(e,uu____1244)::(embedded_state,uu____1246)::[]
                            ->
                            let uu____1313 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Tactics_Embedding.e_proofstate
                                embedded_state
                               in
                            FStar_Util.bind_opt uu____1313
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 let uu____1322 =
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1326  ->
                                        let uu____1327 =
                                          FStar_Ident.string_of_lid nm  in
                                        let uu____1328 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state
                                           in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1327 uu____1328)
                                    in
                                 let uu____1329 =
                                   FStar_Syntax_Embeddings.unembed ea a  in
                                 FStar_Util.bind_opt uu____1329
                                   (fun a1  ->
                                      let uu____1335 =
                                        FStar_Syntax_Embeddings.unembed eb b
                                         in
                                      FStar_Util.bind_opt uu____1335
                                        (fun b1  ->
                                           let uu____1341 =
                                             FStar_Syntax_Embeddings.unembed
                                               ec c
                                              in
                                           FStar_Util.bind_opt uu____1341
                                             (fun c1  ->
                                                let uu____1347 =
                                                  FStar_Syntax_Embeddings.unembed
                                                    ed d
                                                   in
                                                FStar_Util.bind_opt
                                                  uu____1347
                                                  (fun d1  ->
                                                     let uu____1353 =
                                                       FStar_Syntax_Embeddings.unembed
                                                         ee e
                                                        in
                                                     FStar_Util.bind_opt
                                                       uu____1353
                                                       (fun e1  ->
                                                          let res =
                                                            let uu____1363 =
                                                              t a1 b1 c1 d1
                                                                e1
                                                               in
                                                            FStar_Tactics_Basic.run
                                                              uu____1363 ps1
                                                             in
                                                          let uu____1366 =
                                                            let uu____1367 =
                                                              FStar_Tactics_Embedding.e_result
                                                                er
                                                               in
                                                            let uu____1372 =
                                                              FStar_TypeChecker_Normalize.psc_range
                                                                psc
                                                               in
                                                            FStar_Syntax_Embeddings.embed
                                                              uu____1367
                                                              uu____1372 res
                                                             in
                                                          FStar_Pervasives_Native.Some
                                                            uu____1366))))))
                        | uu____1375 ->
                            let uu____1376 =
                              let uu____1377 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____1378 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1377 uu____1378
                               in
                            failwith uu____1376
  
let mk_tactic_interpretation_6 :
  'a 'b 'c 'd 'e 'f 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'c FStar_Syntax_Embeddings.embedding ->
              'd FStar_Syntax_Embeddings.embedding ->
                'e FStar_Syntax_Embeddings.embedding ->
                  'f FStar_Syntax_Embeddings.embedding ->
                    'r FStar_Syntax_Embeddings.embedding ->
                      FStar_Ident.lid ->
                        FStar_TypeChecker_Normalize.psc ->
                          FStar_Syntax_Syntax.args ->
                            FStar_Syntax_Syntax.term
                              FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun ed  ->
              fun ee  ->
                fun ef  ->
                  fun er  ->
                    fun nm  ->
                      fun psc  ->
                        fun args  ->
                          match args with
                          | (a,uu____1551)::(b,uu____1553)::(c,uu____1555)::
                              (d,uu____1557)::(e,uu____1559)::(f,uu____1561)::
                              (embedded_state,uu____1563)::[] ->
                              let uu____1640 =
                                FStar_Syntax_Embeddings.unembed
                                  FStar_Tactics_Embedding.e_proofstate
                                  embedded_state
                                 in
                              FStar_Util.bind_opt uu____1640
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   let uu____1649 =
                                     FStar_Tactics_Basic.log ps1
                                       (fun uu____1653  ->
                                          let uu____1654 =
                                            FStar_Ident.string_of_lid nm  in
                                          let uu____1655 =
                                            FStar_Syntax_Print.term_to_string
                                              embedded_state
                                             in
                                          FStar_Util.print2
                                            "Reached %s, goals are: %s\n"
                                            uu____1654 uu____1655)
                                      in
                                   let uu____1656 =
                                     FStar_Syntax_Embeddings.unembed ea a  in
                                   FStar_Util.bind_opt uu____1656
                                     (fun a1  ->
                                        let uu____1662 =
                                          FStar_Syntax_Embeddings.unembed eb
                                            b
                                           in
                                        FStar_Util.bind_opt uu____1662
                                          (fun b1  ->
                                             let uu____1668 =
                                               FStar_Syntax_Embeddings.unembed
                                                 ec c
                                                in
                                             FStar_Util.bind_opt uu____1668
                                               (fun c1  ->
                                                  let uu____1674 =
                                                    FStar_Syntax_Embeddings.unembed
                                                      ed d
                                                     in
                                                  FStar_Util.bind_opt
                                                    uu____1674
                                                    (fun d1  ->
                                                       let uu____1680 =
                                                         FStar_Syntax_Embeddings.unembed
                                                           ee e
                                                          in
                                                       FStar_Util.bind_opt
                                                         uu____1680
                                                         (fun e1  ->
                                                            let uu____1686 =
                                                              FStar_Syntax_Embeddings.unembed
                                                                ef f
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____1686
                                                              (fun f1  ->
                                                                 let res =
                                                                   let uu____1696
                                                                    =
                                                                    t a1 b1
                                                                    c1 d1 e1
                                                                    f1  in
                                                                   FStar_Tactics_Basic.run
                                                                    uu____1696
                                                                    ps1
                                                                    in
                                                                 let uu____1699
                                                                   =
                                                                   let uu____1700
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                   let uu____1705
                                                                    =
                                                                    FStar_TypeChecker_Normalize.psc_range
                                                                    psc  in
                                                                   FStar_Syntax_Embeddings.embed
                                                                    uu____1700
                                                                    uu____1705
                                                                    res
                                                                    in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____1699)))))))
                          | uu____1708 ->
                              let uu____1709 =
                                let uu____1710 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____1711 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1710 uu____1711
                                 in
                              failwith uu____1709
  
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
  
let rec e_tactic_0' :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____1855  ->
         fun uu____1856  -> failwith "Impossible: embedding tactic (0)?")
      (fun w  ->
         fun t  ->
           let uu____1864 = unembed_tactic_0 er t  in
           FStar_All.pipe_left
             (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____1864)
      FStar_Syntax_Syntax.t_unit

and e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Basic.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____1888  ->
           fun uu____1889  -> failwith "Impossible: embedding tactic (1)?")
        (fun w  -> fun t  -> unembed_tactic_1 ea er t)
        FStar_Syntax_Syntax.t_unit

and (primitive_steps :
  unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____1898  ->
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
    let mktac1 a r name f ea er =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 false f ea er)
       in
    let mktac2 a b r name f ea eb er =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 false f ea eb er)
       in
    let mktac3 a b c r name f ea eb ec er =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 false f ea eb ec er)
       in
    let mktac5 a b c d e r name f ea eb ec ed ee er =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 false f ea eb ec ed ee er)
       in
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____2245)::[] ->
          let uu____2262 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2262
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2270 =
                 let uu____2271 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2272 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2271 uu____2272
                  in
               FStar_Pervasives_Native.Some uu____2270)
      | uu____2273 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____2277 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2277;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____2292)::[] ->
          let uu____2309 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2309
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2317 =
                 let uu____2318 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2319 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2318 uu____2319
                  in
               FStar_Pervasives_Native.Some uu____2317)
      | uu____2320 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____2324 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2324;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____2343)::[] ->
          let uu____2360 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2360
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2370 = FStar_Tactics_Types.tracepoint ps2  in
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2373 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2392)::(r,uu____2394)::[] ->
          let uu____2421 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2421
            (fun ps1  ->
               let uu____2427 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_range r
                  in
               FStar_Util.bind_opt uu____2427
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2435 =
                      let uu____2436 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Syntax_Embeddings.embed
                        FStar_Tactics_Embedding.e_proofstate uu____2436 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2435))
      | uu____2437 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____2454)::(b,uu____2456)::[] ->
          let uu____2483 =
            FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_env
              env_t
             in
          FStar_Util.bind_opt uu____2483
            (fun env  ->
               let uu____2489 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Reflection_Embeddings.e_binder b
                  in
               FStar_Util.bind_opt uu____2489
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____2497 =
                      FStar_Syntax_Embeddings.embed
                        FStar_Reflection_Embeddings.e_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____2497))
      | uu____2498 -> failwith "Unexpected application of push_binder"  in
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
    let uu____2507 =
      let uu____2510 =
        mktac2 () () () "fail"
          (fun a270  ->
             fun a271  ->
               (Obj.magic (fun uu____2512  -> FStar_Tactics_Basic.fail)) a270
                 a271) (Obj.magic FStar_Syntax_Embeddings.e_any)
          (Obj.magic FStar_Syntax_Embeddings.e_string)
          (Obj.magic FStar_Syntax_Embeddings.e_any)
         in
      let uu____2513 =
        let uu____2516 =
          mktac1 () () "trivial"
            (fun a272  -> (Obj.magic FStar_Tactics_Basic.trivial) a272)
            (Obj.magic FStar_Syntax_Embeddings.e_unit)
            (Obj.magic FStar_Syntax_Embeddings.e_unit)
           in
        let uu____2517 =
          let uu____2520 =
            let uu____2521 = e_tactic_0' FStar_Syntax_Embeddings.e_any  in
            let uu____2526 =
              FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any
               in
            mktac2 () () () "__trytac"
              (fun a273  ->
                 fun a274  ->
                   (Obj.magic (fun uu____2532  -> FStar_Tactics_Basic.trytac))
                     a273 a274) (Obj.magic FStar_Syntax_Embeddings.e_any)
              (Obj.magic uu____2521) (Obj.magic uu____2526)
             in
          let uu____2533 =
            let uu____2536 =
              mktac1 () () "intro"
                (fun a275  -> (Obj.magic FStar_Tactics_Basic.intro) a275)
                (Obj.magic FStar_Syntax_Embeddings.e_unit)
                (Obj.magic FStar_Reflection_Embeddings.e_binder)
               in
            let uu____2537 =
              let uu____2540 =
                let uu____2541 =
                  FStar_Syntax_Embeddings.e_tuple2
                    FStar_Reflection_Embeddings.e_binder
                    FStar_Reflection_Embeddings.e_binder
                   in
                mktac1 () () "intro_rec"
                  (fun a276  ->
                     (Obj.magic FStar_Tactics_Basic.intro_rec) a276)
                  (Obj.magic FStar_Syntax_Embeddings.e_unit)
                  (Obj.magic uu____2541)
                 in
              let uu____2548 =
                let uu____2551 =
                  let uu____2552 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Syntax_Embeddings.e_norm_step
                     in
                  mktac1 () () "norm"
                    (fun a277  -> (Obj.magic FStar_Tactics_Basic.norm) a277)
                    (Obj.magic uu____2552)
                    (Obj.magic FStar_Syntax_Embeddings.e_unit)
                   in
                let uu____2557 =
                  let uu____2560 =
                    let uu____2561 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_norm_step
                       in
                    mktac3 () () () () "norm_term_env"
                      (fun a278  ->
                         fun a279  ->
                           fun a280  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a278 a279 a280)
                      (Obj.magic FStar_Reflection_Embeddings.e_env)
                      (Obj.magic uu____2561)
                      (Obj.magic FStar_Reflection_Embeddings.e_term)
                      (Obj.magic FStar_Reflection_Embeddings.e_term)
                     in
                  let uu____2566 =
                    let uu____2569 =
                      let uu____2570 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step
                         in
                      mktac2 () () () "norm_binder_type"
                        (fun a281  ->
                           fun a282  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a281 a282) (Obj.magic uu____2570)
                        (Obj.magic FStar_Reflection_Embeddings.e_binder)
                        (Obj.magic FStar_Syntax_Embeddings.e_unit)
                       in
                    let uu____2575 =
                      let uu____2578 =
                        mktac2 () () () "rename_to"
                          (fun a283  ->
                             fun a284  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a283
                                 a284)
                          (Obj.magic FStar_Reflection_Embeddings.e_binder)
                          (Obj.magic FStar_Syntax_Embeddings.e_string)
                          (Obj.magic FStar_Syntax_Embeddings.e_unit)
                         in
                      let uu____2579 =
                        let uu____2582 =
                          mktac1 () () "binder_retype"
                            (fun a285  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a285)
                            (Obj.magic FStar_Reflection_Embeddings.e_binder)
                            (Obj.magic FStar_Syntax_Embeddings.e_unit)
                           in
                        let uu____2583 =
                          let uu____2586 =
                            mktac1 () () "revert"
                              (fun a286  ->
                                 (Obj.magic FStar_Tactics_Basic.revert) a286)
                              (Obj.magic FStar_Syntax_Embeddings.e_unit)
                              (Obj.magic FStar_Syntax_Embeddings.e_unit)
                             in
                          let uu____2587 =
                            let uu____2590 =
                              mktac1 () () "clear_top"
                                (fun a287  ->
                                   (Obj.magic FStar_Tactics_Basic.clear_top)
                                     a287)
                                (Obj.magic FStar_Syntax_Embeddings.e_unit)
                                (Obj.magic FStar_Syntax_Embeddings.e_unit)
                               in
                            let uu____2591 =
                              let uu____2594 =
                                mktac1 () () "clear"
                                  (fun a288  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a288)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.e_binder)
                                  (Obj.magic FStar_Syntax_Embeddings.e_unit)
                                 in
                              let uu____2595 =
                                let uu____2598 =
                                  mktac1 () () "rewrite"
                                    (fun a289  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a289)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.e_binder)
                                    (Obj.magic FStar_Syntax_Embeddings.e_unit)
                                   in
                                let uu____2599 =
                                  let uu____2602 =
                                    mktac1 () () "smt"
                                      (fun a290  ->
                                         (Obj.magic FStar_Tactics_Basic.smt)
                                           a290)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.e_unit)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.e_unit)
                                     in
                                  let uu____2603 =
                                    let uu____2606 =
                                      mktac1 () () "refine_intro"
                                        (fun a291  ->
                                           (Obj.magic
                                              FStar_Tactics_Basic.refine_intro)
                                             a291)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.e_unit)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.e_unit)
                                       in
                                    let uu____2607 =
                                      let uu____2610 =
                                        mktac2 () () () "t_exact"
                                          (fun a292  ->
                                             fun a293  ->
                                               (Obj.magic
                                                  FStar_Tactics_Basic.t_exact)
                                                 a292 a293)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.e_bool)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.e_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.e_unit)
                                         in
                                      let uu____2611 =
                                        let uu____2614 =
                                          mktac1 () () "apply"
                                            (fun a294  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a294)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.e_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.e_unit)
                                           in
                                        let uu____2615 =
                                          let uu____2618 =
                                            mktac1 () () "apply_raw"
                                              (fun a295  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a295)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.e_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.e_unit)
                                             in
                                          let uu____2619 =
                                            let uu____2622 =
                                              mktac1 () () "apply_lemma"
                                                (fun a296  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a296)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.e_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.e_unit)
                                               in
                                            let uu____2623 =
                                              let uu____2626 =
                                                let uu____2627 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____2632 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____2637 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Syntax_Embeddings.e_any
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a297  ->
                                                     fun a298  ->
                                                       fun a299  ->
                                                         fun a300  ->
                                                           fun a301  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2646
                                                                    ->
                                                                   fun
                                                                    uu____2647
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a297 a298 a299
                                                               a300 a301)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.e_any)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.e_any)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.e_int)
                                                  (Obj.magic uu____2627)
                                                  (Obj.magic uu____2632)
                                                  (Obj.magic uu____2637)
                                                 in
                                              let uu____2648 =
                                                let uu____2651 =
                                                  let uu____2652 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____2657 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  mktac2 () () () "__seq"
                                                    (fun a302  ->
                                                       fun a303  ->
                                                         (Obj.magic
                                                            FStar_Tactics_Basic.seq)
                                                           a302 a303)
                                                    (Obj.magic uu____2652)
                                                    (Obj.magic uu____2657)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.e_unit)
                                                   in
                                                let uu____2662 =
                                                  let uu____2665 =
                                                    mktac1 () ()
                                                      "set_options"
                                                      (fun a304  ->
                                                         (Obj.magic
                                                            FStar_Tactics_Basic.set_options)
                                                           a304)
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.e_string)
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.e_unit)
                                                     in
                                                  let uu____2666 =
                                                    let uu____2669 =
                                                      mktac1 () () "tc"
                                                        (fun a305  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a305)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.e_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.e_term)
                                                       in
                                                    let uu____2670 =
                                                      let uu____2673 =
                                                        mktac1 () ()
                                                          "unshelve"
                                                          (fun a306  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a306)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.e_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.e_unit)
                                                         in
                                                      let uu____2674 =
                                                        let uu____2677 =
                                                          mktac2 () () ()
                                                            "unquote"
                                                            (fun a307  ->
                                                               fun a308  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a307 a308)
                                                            (Obj.magic
                                                               FStar_Syntax_Embeddings.e_any)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.e_term)
                                                            (Obj.magic
                                                               FStar_Syntax_Embeddings.e_any)
                                                           in
                                                        let uu____2678 =
                                                          let uu____2681 =
                                                            mktac1 () ()
                                                              "prune"
                                                              (fun a309  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a309)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.e_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.e_unit)
                                                             in
                                                          let uu____2682 =
                                                            let uu____2685 =
                                                              mktac1 () ()
                                                                "addns"
                                                                (fun a310  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a310)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_unit)
                                                               in
                                                            let uu____2686 =
                                                              let uu____2689
                                                                =
                                                                mktac1 () ()
                                                                  "print"
                                                                  (fun a311 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print)
                                                                    a311)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                 in
                                                              let uu____2690
                                                                =
                                                                let uu____2693
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "debug"
                                                                    (
                                                                    fun a312 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.debug)
                                                                    a312)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                   in
                                                                let uu____2694
                                                                  =
                                                                  let uu____2697
                                                                    =
                                                                    mktac1 ()
                                                                    () "dump"
                                                                    (fun a313
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a313)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                  let uu____2698
                                                                    =
                                                                    let uu____2701
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "dump1"
                                                                    (fun a314
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a314)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2702
                                                                    =
                                                                    let uu____2705
                                                                    =
                                                                    let uu____2706
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a315
                                                                     ->
                                                                    fun a316 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a315 a316)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.e_direction)
                                                                    (Obj.magic
                                                                    uu____2706)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2711
                                                                    =
                                                                    let uu____2714
                                                                    =
                                                                    let uu____2715
                                                                    =
                                                                    let uu____2727
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____2727
                                                                     in
                                                                    let uu____2738
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__topdown_rewrite"
                                                                    (fun a317
                                                                     ->
                                                                    fun a318 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.topdown_rewrite)
                                                                    a317 a318)
                                                                    (Obj.magic
                                                                    uu____2715)
                                                                    (Obj.magic
                                                                    uu____2738)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2743
                                                                    =
                                                                    let uu____2746
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "trefl"
                                                                    (fun a319
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    a319)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2747
                                                                    =
                                                                    let uu____2750
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "later"
                                                                    (fun a320
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    a320)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2751
                                                                    =
                                                                    let uu____2754
                                                                    =
                                                                    mktac1 ()
                                                                    () "dup"
                                                                    (fun a321
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    a321)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2755
                                                                    =
                                                                    let uu____2758
                                                                    =
                                                                    mktac1 ()
                                                                    () "flip"
                                                                    (fun a322
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    a322)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2759
                                                                    =
                                                                    let uu____2762
                                                                    =
                                                                    mktac1 ()
                                                                    () "qed"
                                                                    (fun a323
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    a323)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2763
                                                                    =
                                                                    let uu____2766
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "dismiss"
                                                                    (fun a324
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dismiss)
                                                                    a324)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2767
                                                                    =
                                                                    let uu____2770
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "tadmit"
                                                                    (fun a325
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.tadmit)
                                                                    a325)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2771
                                                                    =
                                                                    let uu____2774
                                                                    =
                                                                    let uu____2775
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "cases"
                                                                    (fun a326
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a326)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    uu____2775)
                                                                     in
                                                                    let uu____2782
                                                                    =
                                                                    let uu____2785
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "top_env"
                                                                    (fun a327
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    a327)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_env)
                                                                     in
                                                                    let uu____2786
                                                                    =
                                                                    let uu____2789
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_env"
                                                                    (fun a328
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    a328)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_env)
                                                                     in
                                                                    let uu____2790
                                                                    =
                                                                    let uu____2793
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_goal"
                                                                    (fun a329
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    a329)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                     in
                                                                    let uu____2794
                                                                    =
                                                                    let uu____2797
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_witness"
                                                                    (fun a330
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    a330)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                     in
                                                                    let uu____2798
                                                                    =
                                                                    let uu____2801
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "inspect"
                                                                    (fun a331
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.inspect)
                                                                    a331)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term_view)
                                                                     in
                                                                    let uu____2802
                                                                    =
                                                                    let uu____2805
                                                                    =
                                                                    mktac1 ()
                                                                    () "pack"
                                                                    (fun a332
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pack)
                                                                    a332)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term_view)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                     in
                                                                    let uu____2806
                                                                    =
                                                                    let uu____2809
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "fresh"
                                                                    (fun a333
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh)
                                                                    a333)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_int)
                                                                     in
                                                                    let uu____2810
                                                                    =
                                                                    let uu____2813
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "ngoals"
                                                                    (fun a334
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals)
                                                                    a334)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_int)
                                                                     in
                                                                    let uu____2814
                                                                    =
                                                                    let uu____2817
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "ngoals_smt"
                                                                    (fun a335
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals_smt)
                                                                    a335)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_int)
                                                                     in
                                                                    let uu____2818
                                                                    =
                                                                    let uu____2821
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "is_guard"
                                                                    (fun a336
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    a336)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_bool)
                                                                     in
                                                                    let uu____2822
                                                                    =
                                                                    let uu____2825
                                                                    =
                                                                    let uu____2826
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "uvar_env"
                                                                    (fun a337
                                                                     ->
                                                                    fun a338 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a337 a338)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_env)
                                                                    (Obj.magic
                                                                    uu____2826)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                     in
                                                                    let uu____2831
                                                                    =
                                                                    let uu____2834
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "unify"
                                                                    (fun a339
                                                                     ->
                                                                    fun a340 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a339 a340)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_bool)
                                                                     in
                                                                    let uu____2835
                                                                    =
                                                                    let uu____2838
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "launch_process"
                                                                    (fun a341
                                                                     ->
                                                                    fun a342 
                                                                    ->
                                                                    fun a343 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a341 a342
                                                                    a343)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                     in
                                                                    let uu____2839
                                                                    =
                                                                    let uu____2842
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "fresh_bv_named"
                                                                    (fun a344
                                                                     ->
                                                                    fun a345 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_bv_named)
                                                                    a344 a345)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_bv)
                                                                     in
                                                                    let uu____2843
                                                                    =
                                                                    let uu____2846
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "change"
                                                                    (fun a346
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.change)
                                                                    a346)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2847
                                                                    =
                                                                    let uu____2850
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "get_guard_policy"
                                                                    (fun a347
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.get_guard_policy)
                                                                    a347)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.e_guard_policy)
                                                                     in
                                                                    let uu____2851
                                                                    =
                                                                    let uu____2854
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "set_guard_policy"
                                                                    (fun a348
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.set_guard_policy)
                                                                    a348)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.e_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    [uu____2854;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____2850
                                                                    ::
                                                                    uu____2851
                                                                     in
                                                                    uu____2846
                                                                    ::
                                                                    uu____2847
                                                                     in
                                                                    uu____2842
                                                                    ::
                                                                    uu____2843
                                                                     in
                                                                    uu____2838
                                                                    ::
                                                                    uu____2839
                                                                     in
                                                                    uu____2834
                                                                    ::
                                                                    uu____2835
                                                                     in
                                                                    uu____2825
                                                                    ::
                                                                    uu____2831
                                                                     in
                                                                    uu____2821
                                                                    ::
                                                                    uu____2822
                                                                     in
                                                                    uu____2817
                                                                    ::
                                                                    uu____2818
                                                                     in
                                                                    uu____2813
                                                                    ::
                                                                    uu____2814
                                                                     in
                                                                    uu____2809
                                                                    ::
                                                                    uu____2810
                                                                     in
                                                                    uu____2805
                                                                    ::
                                                                    uu____2806
                                                                     in
                                                                    uu____2801
                                                                    ::
                                                                    uu____2802
                                                                     in
                                                                    uu____2797
                                                                    ::
                                                                    uu____2798
                                                                     in
                                                                    uu____2793
                                                                    ::
                                                                    uu____2794
                                                                     in
                                                                    uu____2789
                                                                    ::
                                                                    uu____2790
                                                                     in
                                                                    uu____2785
                                                                    ::
                                                                    uu____2786
                                                                     in
                                                                    uu____2774
                                                                    ::
                                                                    uu____2782
                                                                     in
                                                                    uu____2770
                                                                    ::
                                                                    uu____2771
                                                                     in
                                                                    uu____2766
                                                                    ::
                                                                    uu____2767
                                                                     in
                                                                    uu____2762
                                                                    ::
                                                                    uu____2763
                                                                     in
                                                                    uu____2758
                                                                    ::
                                                                    uu____2759
                                                                     in
                                                                    uu____2754
                                                                    ::
                                                                    uu____2755
                                                                     in
                                                                    uu____2750
                                                                    ::
                                                                    uu____2751
                                                                     in
                                                                    uu____2746
                                                                    ::
                                                                    uu____2747
                                                                     in
                                                                    uu____2714
                                                                    ::
                                                                    uu____2743
                                                                     in
                                                                    uu____2705
                                                                    ::
                                                                    uu____2711
                                                                     in
                                                                    uu____2701
                                                                    ::
                                                                    uu____2702
                                                                     in
                                                                  uu____2697
                                                                    ::
                                                                    uu____2698
                                                                   in
                                                                uu____2693 ::
                                                                  uu____2694
                                                                 in
                                                              uu____2689 ::
                                                                uu____2690
                                                               in
                                                            uu____2685 ::
                                                              uu____2686
                                                             in
                                                          uu____2681 ::
                                                            uu____2682
                                                           in
                                                        uu____2677 ::
                                                          uu____2678
                                                         in
                                                      uu____2673 ::
                                                        uu____2674
                                                       in
                                                    uu____2669 :: uu____2670
                                                     in
                                                  uu____2665 :: uu____2666
                                                   in
                                                uu____2651 :: uu____2662  in
                                              uu____2626 :: uu____2648  in
                                            uu____2622 :: uu____2623  in
                                          uu____2618 :: uu____2619  in
                                        uu____2614 :: uu____2615  in
                                      uu____2610 :: uu____2611  in
                                    uu____2606 :: uu____2607  in
                                  uu____2602 :: uu____2603  in
                                uu____2598 :: uu____2599  in
                              uu____2594 :: uu____2595  in
                            uu____2590 :: uu____2591  in
                          uu____2586 :: uu____2587  in
                        uu____2582 :: uu____2583  in
                      uu____2578 :: uu____2579  in
                    uu____2569 :: uu____2575  in
                  uu____2560 :: uu____2566  in
                uu____2551 :: uu____2557  in
              uu____2540 :: uu____2548  in
            uu____2536 :: uu____2537  in
          uu____2520 :: uu____2533  in
        uu____2516 :: uu____2517  in
      uu____2510 :: uu____2513  in
    FStar_List.append uu____2507
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)

and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          ('Aa -> 'Ar FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        FStar_Pervasives_Native.Some
          (fun x  ->
             let rng = FStar_Range.dummyRange  in
             let x_tm = FStar_Syntax_Embeddings.embed ea rng x  in
             let app =
               let uu____2877 =
                 let uu____2880 =
                   let uu____2881 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____2881]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____2880  in
               uu____2877 FStar_Pervasives_Native.None rng  in
             unembed_tactic_0 er app)

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun embedded_tac_b  ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state  ->
           let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
           let tm =
             let uu____2904 =
               let uu____2907 =
                 let uu____2908 =
                   let uu____2909 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2909  in
                 [uu____2908]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2907  in
             uu____2904 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           let uu____2915 =
             let uu____2916 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2916
             then
               let uu____2917 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "Starting normalizer with %s\n" uu____2917
             else ()  in
           let result =
             let uu____2920 = primitive_steps ()  in
             FStar_TypeChecker_Normalize.normalize_with_primitive_steps
               uu____2920 steps proof_state.FStar_Tactics_Types.main_context
               tm
              in
           let uu____2923 =
             let uu____2924 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2924
             then
               let uu____2925 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2925
             else ()  in
           let res =
             let uu____2932 = FStar_Tactics_Embedding.e_result eb  in
             FStar_Syntax_Embeddings.unembed uu____2932 result  in
           match res with
           | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
               (b,ps)) ->
               let uu____2945 = FStar_Tactics_Basic.set ps  in
               FStar_Tactics_Basic.bind uu____2945
                 (fun uu____2949  -> FStar_Tactics_Basic.ret b)
           | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
               (msg,ps)) ->
               let uu____2954 = FStar_Tactics_Basic.set ps  in
               FStar_Tactics_Basic.bind uu____2954
                 (fun uu____2958  -> FStar_Tactics_Basic.fail msg)
           | FStar_Pervasives_Native.None  ->
               let uu____2961 =
                 let uu____2966 =
                   let uu____2967 = FStar_Syntax_Print.term_to_string result
                      in
                   FStar_Util.format1
                     "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                     uu____2967
                    in
                 (FStar_Errors.Fatal_TacticGotStuck, uu____2966)  in
               FStar_Errors.raise_error uu____2961
                 (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      let uu____2974 = unembed_tactic_0 eb embedded_tac_b  in
      FStar_All.pipe_left (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
        uu____2974

let (report_implicits :
  FStar_Tactics_Types.proofstate -> FStar_TypeChecker_Env.implicits -> unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____3030  ->
             match uu____3030 with
             | (r,uu____3050,uv,uu____3052,ty,rng) ->
                 let uu____3055 =
                   let uu____3056 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____3057 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____3056 uu____3057 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____3055, rng)) is
         in
      match errs with
      | [] -> ()
      | (e,msg,r)::tl1 ->
          let uu____3082 =
            FStar_Tactics_Basic.dump_proofstate ps
              "failing due to uninstantiated implicits"
             in
          let uu____3083 = FStar_Errors.add_errors tl1  in
          FStar_Errors.raise_error (e, msg) r
  
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
        let uu____3111 =
          let uu____3112 = FStar_ST.op_Bang tacdbg  in
          if uu____3112
          then
            let uu____3136 = FStar_Syntax_Print.term_to_string tactic  in
            FStar_Util.print1 "About to reduce uvars on: %s\n" uu____3136
          else ()  in
        let tactic1 =
          FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
        let uu____3139 =
          let uu____3140 = FStar_ST.op_Bang tacdbg  in
          if uu____3140
          then
            let uu____3164 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____3164
          else ()  in
        let uu____3166 =
          FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
        match uu____3166 with
        | (uu____3179,uu____3180,g) ->
            let uu____3182 = FStar_TypeChecker_Rel.force_trivial_guard env g
               in
            let uu____3183 = FStar_Errors.stop_if_err ()  in
            let tau = unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic1
               in
            let uu____3187 = FStar_TypeChecker_Env.clear_expected_typ env  in
            (match uu____3187 with
             | (env1,uu____3201) ->
                 let env2 =
                   let uu___60_3207 = env1  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___60_3207.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___60_3207.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___60_3207.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___60_3207.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___60_3207.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___60_3207.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___60_3207.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___60_3207.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___60_3207.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp = false;
                     FStar_TypeChecker_Env.effects =
                       (uu___60_3207.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___60_3207.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___60_3207.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___60_3207.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___60_3207.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___60_3207.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___60_3207.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___60_3207.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax =
                       (uu___60_3207.FStar_TypeChecker_Env.lax);
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___60_3207.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.failhard =
                       (uu___60_3207.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___60_3207.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___60_3207.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___60_3207.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___60_3207.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___60_3207.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___60_3207.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___60_3207.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___60_3207.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___60_3207.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___60_3207.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___60_3207.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___60_3207.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___60_3207.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___60_3207.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___60_3207.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.dep_graph =
                       (uu___60_3207.FStar_TypeChecker_Env.dep_graph)
                   }  in
                 let env3 =
                   let uu___61_3209 = env2  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___61_3209.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___61_3209.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___61_3209.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___61_3209.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___61_3209.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___61_3209.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___61_3209.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___61_3209.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___61_3209.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___61_3209.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___61_3209.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___61_3209.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___61_3209.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___61_3209.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___61_3209.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___61_3209.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___61_3209.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___61_3209.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax =
                       (uu___61_3209.FStar_TypeChecker_Env.lax);
                     FStar_TypeChecker_Env.lax_universes = true;
                     FStar_TypeChecker_Env.failhard =
                       (uu___61_3209.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___61_3209.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___61_3209.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___61_3209.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___61_3209.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___61_3209.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___61_3209.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___61_3209.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___61_3209.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___61_3209.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___61_3209.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___61_3209.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___61_3209.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___61_3209.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___61_3209.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___61_3209.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.dep_graph =
                       (uu___61_3209.FStar_TypeChecker_Env.dep_graph)
                   }  in
                 let uu____3210 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ  in
                 (match uu____3210 with
                  | (ps,w) ->
                      let uu____3223 =
                        let uu____3224 = FStar_ST.op_Bang tacdbg  in
                        if uu____3224
                        then
                          let uu____3248 =
                            FStar_Syntax_Print.term_to_string typ  in
                          FStar_Util.print1 "Running tactic with goal = %s\n"
                            uu____3248
                        else ()  in
                      let uu____3250 =
                        FStar_Util.record_time
                          (fun uu____3260  -> FStar_Tactics_Basic.run tau ps)
                         in
                      (match uu____3250 with
                       | (res,ms) ->
                           let uu____3273 =
                             let uu____3274 = FStar_ST.op_Bang tacdbg  in
                             if uu____3274
                             then
                               let uu____3298 =
                                 FStar_Syntax_Print.term_to_string tactic1
                                  in
                               let uu____3299 = FStar_Util.string_of_int ms
                                  in
                               let uu____3300 =
                                 FStar_Syntax_Print.lid_to_string
                                   env3.FStar_TypeChecker_Env.curmodule
                                  in
                               FStar_Util.print3
                                 "Tactic %s ran in %s ms (%s)\n" uu____3298
                                 uu____3299 uu____3300
                             else ()  in
                           (match res with
                            | FStar_Tactics_Result.Success (uu____3308,ps1)
                                ->
                                let uu____3310 =
                                  let uu____3311 = FStar_ST.op_Bang tacdbg
                                     in
                                  if uu____3311
                                  then
                                    let uu____3335 =
                                      FStar_Syntax_Print.term_to_string w  in
                                    FStar_Util.print1
                                      "Tactic generated proofterm %s\n"
                                      uu____3335
                                  else ()  in
                                let uu____3337 =
                                  FStar_List.iter
                                    (fun g1  ->
                                       let uu____3342 =
                                         FStar_Tactics_Basic.is_irrelevant g1
                                          in
                                       if uu____3342
                                       then
                                         let uu____3343 =
                                           FStar_TypeChecker_Rel.teq_nosmt
                                             g1.FStar_Tactics_Types.context
                                             g1.FStar_Tactics_Types.witness
                                             FStar_Syntax_Util.exp_unit
                                            in
                                         (if uu____3343
                                          then ()
                                          else
                                            (let uu____3345 =
                                               let uu____3346 =
                                                 FStar_Syntax_Print.term_to_string
                                                   g1.FStar_Tactics_Types.witness
                                                  in
                                               FStar_Util.format1
                                                 "Irrelevant tactic witness does not unify with (): %s"
                                                 uu____3346
                                                in
                                             failwith uu____3345))
                                       else ())
                                    (FStar_List.append
                                       ps1.FStar_Tactics_Types.goals
                                       ps1.FStar_Tactics_Types.smt_goals)
                                   in
                                let g1 =
                                  let uu___62_3349 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___62_3349.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___62_3349.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___62_3349.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (ps1.FStar_Tactics_Types.all_implicits)
                                  }  in
                                let g2 =
                                  let uu____3351 =
                                    FStar_TypeChecker_Rel.solve_deferred_constraints
                                      env3 g1
                                     in
                                  FStar_All.pipe_right uu____3351
                                    FStar_TypeChecker_Rel.resolve_implicits_tac
                                   in
                                let uu____3352 =
                                  report_implicits ps1
                                    g2.FStar_TypeChecker_Env.implicits
                                   in
                                ((FStar_List.append
                                    ps1.FStar_Tactics_Types.goals
                                    ps1.FStar_Tactics_Types.smt_goals), w)
                            | FStar_Tactics_Result.Failed (s,ps1) ->
                                let uu____3357 =
                                  let uu____3358 =
                                    let uu____3359 =
                                      FStar_TypeChecker_Normalize.psc_subst
                                        ps1.FStar_Tactics_Types.psc
                                       in
                                    FStar_Tactics_Types.subst_proof_state
                                      uu____3359 ps1
                                     in
                                  FStar_Tactics_Basic.dump_proofstate
                                    uu____3358 "at the time of failure"
                                   in
                                let uu____3360 =
                                  let uu____3365 =
                                    FStar_Util.format1
                                      "user tactic failed: %s" s
                                     in
                                  (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                    uu____3365)
                                   in
                                FStar_Errors.raise_error uu____3360
                                  typ.FStar_Syntax_Syntax.pos))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____3377 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____3383 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____3389 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3441 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3481 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3535 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3576 . 'Auu____3576 -> 'Auu____3576 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3604 = FStar_Syntax_Util.head_and_args t  in
        match uu____3604 with
        | (hd1,args) ->
            let uu____3641 =
              let uu____3654 =
                let uu____3655 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3655.FStar_Syntax_Syntax.n  in
              (uu____3654, args)  in
            (match uu____3641 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3668))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3731 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3731 with
                       | (gs,uu____3739) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3746 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3746 with
                       | (gs,uu____3754) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3805 =
                        let uu____3812 =
                          let uu____3815 =
                            let uu____3816 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3816
                             in
                          [uu____3815]  in
                        (FStar_Syntax_Util.t_true, uu____3812)  in
                      Simplified uu____3805
                  | Both  ->
                      let uu____3827 =
                        let uu____3840 =
                          let uu____3843 =
                            let uu____3844 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3844
                             in
                          [uu____3843]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3840)  in
                      Dual uu____3827
                  | Neg  -> Simplified (assertion, []))
             | uu____3865 -> Unchanged t)
  
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
    fun uu___59_3953  ->
      match uu___59_3953 with
      | Unchanged t -> let uu____3959 = f t  in Unchanged uu____3959
      | Simplified (t,gs) ->
          let uu____3966 = let uu____3973 = f t  in (uu____3973, gs)  in
          Simplified uu____3966
      | Dual (tn,tp,gs) ->
          let uu____3983 =
            let uu____3992 = f tn  in
            let uu____3993 = f tp  in (uu____3992, uu____3993, gs)  in
          Dual uu____3983
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____4056 = f t1 t2  in Unchanged uu____4056
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____4068 = let uu____4075 = f t1 t2  in (uu____4075, gs)
               in
            Simplified uu____4068
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____4089 = let uu____4096 = f t1 t2  in (uu____4096, gs)
               in
            Simplified uu____4089
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____4115 =
              let uu____4122 = f t1 t2  in
              (uu____4122, (FStar_List.append gs1 gs2))  in
            Simplified uu____4115
        | uu____4125 ->
            let uu____4134 = explode x  in
            (match uu____4134 with
             | (n1,p1,gs1) ->
                 let uu____4152 = explode y  in
                 (match uu____4152 with
                  | (n2,p2,gs2) ->
                      let uu____4170 =
                        let uu____4179 = f n1 n2  in
                        let uu____4180 = f p1 p2  in
                        (uu____4179, uu____4180, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____4170))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____4250 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____4250
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____4298  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____4340 =
              let uu____4341 = FStar_Syntax_Subst.compress t  in
              uu____4341.FStar_Syntax_Syntax.n  in
            match uu____4340 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____4353 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____4353 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____4378 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____4378 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4397;
                   FStar_Syntax_Syntax.vars = uu____4398;_},(p,uu____4400)::
                 (q,uu____4402)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____4442 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4442
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____4445 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____4445 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4451 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4451.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4455;
                   FStar_Syntax_Syntax.vars = uu____4456;_},(p,uu____4458)::
                 (q,uu____4460)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4500 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4500
                   in
                let xq =
                  let uu____4502 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4502
                   in
                let r1 =
                  let uu____4504 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4504 p  in
                let r2 =
                  let uu____4506 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4506 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4509,Unchanged uu____4510) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4520 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4520.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4523 ->
                     let uu____4528 = explode r1  in
                     (match uu____4528 with
                      | (pn,pp,gs1) ->
                          let uu____4546 = explode r2  in
                          (match uu____4546 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4567 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4568 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4567
                                   uu____4568
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4620  ->
                       fun r  ->
                         match uu____4620 with
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
                let uu____4738 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4738 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4772  ->
                            match uu____4772 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4786 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___63_4811 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___63_4811.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___63_4811.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4786 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4831 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4831.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4877 = traverse f pol e t1  in
                let uu____4882 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4882 uu____4877
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___64_4921 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___64_4921.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___64_4921.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4928 =
                f pol e
                  (let uu___65_4932 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___65_4932.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___65_4932.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4928
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___66_4942 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___66_4942.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___66_4942.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4943 = explode rp  in
              (match uu____4943 with
               | (uu____4952,p',gs') ->
                   Dual
                     ((let uu___67_4966 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___67_4966.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___67_4966.FStar_Syntax_Syntax.vars)
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
      let uu____5008 =
        let uu____5009 =
          FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
        FStar_ST.op_Colon_Equals tacdbg uu____5009  in
      let uu____5033 =
        let uu____5034 = FStar_ST.op_Bang tacdbg  in
        if uu____5034
        then
          let uu____5058 =
            let uu____5059 = FStar_TypeChecker_Env.all_binders env  in
            FStar_All.pipe_right uu____5059
              (FStar_Syntax_Print.binders_to_string ",")
             in
          let uu____5060 = FStar_Syntax_Print.term_to_string goal  in
          FStar_Util.print2 "About to preprocess %s |= %s\n" uu____5058
            uu____5060
        else ()  in
      let initial = ((Prims.parse_int "1"), [])  in
      let uu____5089 =
        let uu____5096 = traverse by_tactic_interp Pos env goal  in
        match uu____5096 with
        | Unchanged t' -> (t', [])
        | Simplified (t',gs) -> (t', gs)
        | uu____5114 -> failwith "no"  in
      match uu____5089 with
      | (t',gs) ->
          let uu____5135 =
            let uu____5136 = FStar_ST.op_Bang tacdbg  in
            if uu____5136
            then
              let uu____5160 =
                let uu____5161 = FStar_TypeChecker_Env.all_binders env  in
                FStar_All.pipe_right uu____5161
                  (FStar_Syntax_Print.binders_to_string ", ")
                 in
              let uu____5162 = FStar_Syntax_Print.term_to_string t'  in
              FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                uu____5160 uu____5162
            else ()  in
          let s = initial  in
          let s1 =
            FStar_List.fold_left
              (fun uu____5209  ->
                 fun g  ->
                   match uu____5209 with
                   | (n1,gs1) ->
                       let phi =
                         let uu____5254 =
                           getprop g.FStar_Tactics_Types.context
                             g.FStar_Tactics_Types.goal_ty
                            in
                         match uu____5254 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____5257 =
                               let uu____5262 =
                                 let uu____5263 =
                                   FStar_Syntax_Print.term_to_string
                                     g.FStar_Tactics_Types.goal_ty
                                    in
                                 FStar_Util.format1
                                   "Tactic returned proof-relevant goal: %s"
                                   uu____5263
                                  in
                               (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                 uu____5262)
                                in
                             FStar_Errors.raise_error uu____5257
                               env.FStar_TypeChecker_Env.range
                         | FStar_Pervasives_Native.Some phi -> phi  in
                       let uu____5265 =
                         let uu____5266 = FStar_ST.op_Bang tacdbg  in
                         if uu____5266
                         then
                           let uu____5290 = FStar_Util.string_of_int n1  in
                           let uu____5291 =
                             FStar_Tactics_Basic.goal_to_string g  in
                           FStar_Util.print2 "Got goal #%s: %s\n" uu____5290
                             uu____5291
                         else ()  in
                       let gt' =
                         let uu____5294 =
                           let uu____5295 = FStar_Util.string_of_int n1  in
                           Prims.strcat "Could not prove goal #" uu____5295
                            in
                         FStar_TypeChecker_Util.label uu____5294
                           goal.FStar_Syntax_Syntax.pos phi
                          in
                       ((n1 + (Prims.parse_int "1")),
                         (((g.FStar_Tactics_Types.context), gt',
                            (g.FStar_Tactics_Types.opts)) :: gs1))) s gs
             in
          let uu____5310 = s1  in
          (match uu____5310 with
           | (uu____5331,gs1) ->
               let uu____5349 =
                 let uu____5356 = FStar_Options.peek ()  in
                 (env, t', uu____5356)  in
               uu____5349 :: gs1)
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____5369 =
        let uu____5370 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____5370  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____5369 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____5371 =
      let uu____5374 =
        let uu____5375 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____5376 =
          let uu____5379 = FStar_Syntax_Syntax.as_arg a  in [uu____5379]  in
        uu____5375 :: uu____5376  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____5374  in
    uu____5371 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let uu____5397 =
          let uu____5398 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____5398  in
        let uu____5422 =
          let uu____5429 = reify_tactic tau  in
          run_tactic_on_typ uu____5429 env typ  in
        match uu____5422 with
        | (gs,w) ->
            let uu____5436 =
              FStar_List.existsML
                (fun g  ->
                   let uu____5440 =
                     let uu____5441 =
                       getprop g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Option.isSome uu____5441  in
                   Prims.op_Negation uu____5440) gs
               in
            if uu____5436
            then
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                  "synthesis left open goals") typ.FStar_Syntax_Syntax.pos
            else w
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      let uu____5459 =
        let uu____5460 =
          FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
        FStar_ST.op_Colon_Equals tacdbg uu____5460  in
      let typ = FStar_Syntax_Syntax.t_decls  in
      let uu____5485 =
        let uu____5492 = reify_tactic tau  in
        run_tactic_on_typ uu____5492 env typ  in
      match uu____5485 with
      | (gs,w) ->
          let uu____5501 =
            let uu____5502 =
              FStar_List.existsML
                (fun g  ->
                   let uu____5506 =
                     let uu____5507 =
                       getprop g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Option.isSome uu____5507  in
                   Prims.op_Negation uu____5506) gs
               in
            if uu____5502
            then
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                  "splice left open goals") typ.FStar_Syntax_Syntax.pos
            else ()  in
          let w1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Weak;
              FStar_TypeChecker_Normalize.HNF;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant;
              FStar_TypeChecker_Normalize.Primops;
              FStar_TypeChecker_Normalize.Unascribe;
              FStar_TypeChecker_Normalize.Unmeta] env w
             in
          let uu____5512 =
            let uu____5517 =
              FStar_Syntax_Embeddings.e_list
                FStar_Reflection_Embeddings.e_sigelt
               in
            FStar_Syntax_Embeddings.unembed uu____5517 w1  in
          FStar_All.pipe_left FStar_Util.must uu____5512
  