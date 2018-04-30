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
                       FStar_Tactics_Basic.log ps1
                         (fun uu____100  ->
                            let uu____101 = FStar_Ident.string_of_lid nm  in
                            let uu____102 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____101 uu____102);
                       (let res =
                          let uu____104 = FStar_Tactics_Embedding.e_result er
                             in
                          let uu____109 =
                            FStar_TypeChecker_Normalize.psc_range psc  in
                          let uu____110 = FStar_Tactics_Basic.run t ps1  in
                          FStar_Syntax_Embeddings.embed uu____104 uu____109
                            uu____110
                           in
                        FStar_Pervasives_Native.Some res))
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
                         FStar_Tactics_Basic.log ps1
                           (fun uu____235  ->
                              let uu____236 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____237 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____236 uu____237);
                         (let uu____238 =
                            FStar_Syntax_Embeddings.unembed ea a  in
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
                               FStar_Pervasives_Native.Some uu____251)))
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
                         FStar_Tactics_Basic.log ps1
                           (fun uu____388  ->
                              let uu____389 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____390 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____389 uu____390);
                         (let uu____391 =
                            FStar_Syntax_Embeddings.unembed ea a  in
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
                               FStar_Pervasives_Native.Some uu____404)))
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
                           FStar_Tactics_Basic.log ps1
                             (fun uu____567  ->
                                let uu____568 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____569 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____568
                                  uu____569);
                           (let uu____570 =
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
                                      FStar_Pervasives_Native.Some uu____589))))
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
                                    uu____785);
                             (let uu____786 =
                                FStar_Syntax_Embeddings.unembed ea a  in
                              FStar_Util.bind_opt uu____786
                                (fun a1  ->
                                   let uu____792 =
                                     FStar_Syntax_Embeddings.unembed eb b  in
                                   FStar_Util.bind_opt uu____792
                                     (fun b1  ->
                                        let uu____798 =
                                          FStar_Syntax_Embeddings.unembed ec
                                            c
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
                                               uu____811)))))
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
                                      uu____1037 uu____1038);
                               (let uu____1039 =
                                  FStar_Syntax_Embeddings.unembed ea a  in
                                FStar_Util.bind_opt uu____1039
                                  (fun a1  ->
                                     let uu____1045 =
                                       FStar_Syntax_Embeddings.unembed eb b
                                        in
                                     FStar_Util.bind_opt uu____1045
                                       (fun b1  ->
                                          let uu____1051 =
                                            FStar_Syntax_Embeddings.unembed
                                              ec c
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
                                                      uu____1070))))))
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
                                        uu____1327 uu____1328);
                                 (let uu____1329 =
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
                                                             uu____1366)))))))
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
                                          uu____1654 uu____1655);
                                   (let uu____1656 =
                                      FStar_Syntax_Embeddings.unembed ea a
                                       in
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
                                                                    ps1  in
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
                                                                    res  in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____1699))))))))
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
    let mktac1 name f ea er =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 false f ea er)
       in
    let mktac2 name f ea eb er =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 false f ea eb er)
       in
    let mktac3 name f ea eb ec er =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 false f ea eb ec er)
       in
    let mktac5 name f ea eb ec ed ee er =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 false f ea eb ec ed ee er)
       in
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____2304)::[] ->
          let uu____2321 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2321
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2329 =
                 let uu____2330 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2331 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2330 uu____2331
                  in
               FStar_Pervasives_Native.Some uu____2329)
      | uu____2332 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____2336 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2336;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____2353)::[] ->
          let uu____2370 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2370
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2378 =
                 let uu____2379 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2380 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2379 uu____2380
                  in
               FStar_Pervasives_Native.Some uu____2378)
      | uu____2381 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____2385 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2385;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____2406)::[] ->
          let uu____2423 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2423
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2436 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2457)::(r,uu____2459)::[] ->
          let uu____2486 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2486
            (fun ps1  ->
               let uu____2492 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_range r
                  in
               FStar_Util.bind_opt uu____2492
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2500 =
                      let uu____2501 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Syntax_Embeddings.embed
                        FStar_Tactics_Embedding.e_proofstate uu____2501 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2500))
      | uu____2502 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____2521)::(b,uu____2523)::[] ->
          let uu____2550 =
            FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_env
              env_t
             in
          FStar_Util.bind_opt uu____2550
            (fun env  ->
               let uu____2556 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Reflection_Embeddings.e_binder b
                  in
               FStar_Util.bind_opt uu____2556
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____2572 =
                      FStar_Syntax_Embeddings.embed
                        FStar_Reflection_Embeddings.e_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____2572))
      | uu____2573 -> failwith "Unexpected application of push_binder"  in
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
    let uu____2582 =
      let uu____2585 =
        mktac2 "fail" (fun uu____2587  -> FStar_Tactics_Basic.fail)
          FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string
          FStar_Syntax_Embeddings.e_any
         in
      let uu____2588 =
        let uu____2591 =
          mktac1 "trivial" FStar_Tactics_Basic.trivial
            FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
           in
        let uu____2592 =
          let uu____2595 =
            let uu____2596 = e_tactic_0' FStar_Syntax_Embeddings.e_any  in
            let uu____2601 =
              FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any
               in
            mktac2 "__trytac" (fun uu____2611  -> FStar_Tactics_Basic.trytac)
              FStar_Syntax_Embeddings.e_any uu____2596 uu____2601
             in
          let uu____2612 =
            let uu____2615 =
              mktac1 "intro" FStar_Tactics_Basic.intro
                FStar_Syntax_Embeddings.e_unit
                FStar_Reflection_Embeddings.e_binder
               in
            let uu____2616 =
              let uu____2619 =
                let uu____2620 =
                  FStar_Syntax_Embeddings.e_tuple2
                    FStar_Reflection_Embeddings.e_binder
                    FStar_Reflection_Embeddings.e_binder
                   in
                mktac1 "intro_rec" FStar_Tactics_Basic.intro_rec
                  FStar_Syntax_Embeddings.e_unit uu____2620
                 in
              let uu____2631 =
                let uu____2634 =
                  let uu____2635 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Syntax_Embeddings.e_norm_step
                     in
                  mktac1 "norm" FStar_Tactics_Basic.norm uu____2635
                    FStar_Syntax_Embeddings.e_unit
                   in
                let uu____2642 =
                  let uu____2645 =
                    let uu____2646 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_norm_step
                       in
                    mktac3 "norm_term_env" FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Embeddings.e_env uu____2646
                      FStar_Reflection_Embeddings.e_term
                      FStar_Reflection_Embeddings.e_term
                     in
                  let uu____2653 =
                    let uu____2656 =
                      let uu____2657 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step
                         in
                      mktac2 "norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____2657
                        FStar_Reflection_Embeddings.e_binder
                        FStar_Syntax_Embeddings.e_unit
                       in
                    let uu____2664 =
                      let uu____2667 =
                        mktac2 "rename_to" FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_string
                          FStar_Syntax_Embeddings.e_unit
                         in
                      let uu____2668 =
                        let uu____2671 =
                          mktac1 "binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_unit
                           in
                        let uu____2672 =
                          let uu____2675 =
                            mktac1 "revert" FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Syntax_Embeddings.e_unit
                             in
                          let uu____2676 =
                            let uu____2679 =
                              mktac1 "clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit
                               in
                            let uu____2680 =
                              let uu____2683 =
                                mktac1 "clear" FStar_Tactics_Basic.clear
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                 in
                              let uu____2684 =
                                let uu____2687 =
                                  mktac1 "rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_unit
                                   in
                                let uu____2688 =
                                  let uu____2691 =
                                    mktac1 "smt" FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                     in
                                  let uu____2692 =
                                    let uu____2695 =
                                      mktac1 "refine_intro"
                                        FStar_Tactics_Basic.refine_intro
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                       in
                                    let uu____2696 =
                                      let uu____2699 =
                                        mktac2 "t_exact"
                                          FStar_Tactics_Basic.t_exact
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Syntax_Embeddings.e_unit
                                         in
                                      let uu____2700 =
                                        let uu____2703 =
                                          mktac1 "apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_unit
                                           in
                                        let uu____2704 =
                                          let uu____2707 =
                                            mktac1 "apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Embeddings.e_term
                                              FStar_Syntax_Embeddings.e_unit
                                             in
                                          let uu____2708 =
                                            let uu____2711 =
                                              mktac1 "apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Syntax_Embeddings.e_unit
                                               in
                                            let uu____2712 =
                                              let uu____2715 =
                                                let uu____2716 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____2721 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____2726 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Syntax_Embeddings.e_any
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                mktac5 "__divide"
                                                  (fun uu____2743  ->
                                                     fun uu____2744  ->
                                                       FStar_Tactics_Basic.divide)
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_int
                                                  uu____2716 uu____2721
                                                  uu____2726
                                                 in
                                              let uu____2745 =
                                                let uu____2748 =
                                                  let uu____2749 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____2754 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  mktac2 "__seq"
                                                    FStar_Tactics_Basic.seq
                                                    uu____2749 uu____2754
                                                    FStar_Syntax_Embeddings.e_unit
                                                   in
                                                let uu____2763 =
                                                  let uu____2766 =
                                                    mktac1 "set_options"
                                                      FStar_Tactics_Basic.set_options
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____2767 =
                                                    let uu____2770 =
                                                      mktac1 "tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Reflection_Embeddings.e_term
                                                       in
                                                    let uu____2771 =
                                                      let uu____2774 =
                                                        mktac1 "unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_unit
                                                         in
                                                      let uu____2775 =
                                                        let uu____2778 =
                                                          mktac2 "unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Reflection_Embeddings.e_term
                                                            FStar_Syntax_Embeddings.e_any
                                                           in
                                                        let uu____2779 =
                                                          let uu____2782 =
                                                            mktac1 "prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.e_string
                                                              FStar_Syntax_Embeddings.e_unit
                                                             in
                                                          let uu____2783 =
                                                            let uu____2786 =
                                                              mktac1 "addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____2787 =
                                                              let uu____2790
                                                                =
                                                                mktac1
                                                                  "print"
                                                                  FStar_Tactics_Basic.print
                                                                  FStar_Syntax_Embeddings.e_string
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                 in
                                                              let uu____2791
                                                                =
                                                                let uu____2794
                                                                  =
                                                                  mktac1
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                   in
                                                                let uu____2795
                                                                  =
                                                                  let uu____2798
                                                                    =
                                                                    mktac1
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                  let uu____2799
                                                                    =
                                                                    let uu____2802
                                                                    =
                                                                    mktac1
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2803
                                                                    =
                                                                    let uu____2806
                                                                    =
                                                                    let uu____2807
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____2807
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2814
                                                                    =
                                                                    let uu____2817
                                                                    =
                                                                    let uu____2818
                                                                    =
                                                                    let uu____2830
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____2830
                                                                     in
                                                                    let uu____2841
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____2818
                                                                    uu____2841
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2857
                                                                    =
                                                                    let uu____2860
                                                                    =
                                                                    mktac1
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2861
                                                                    =
                                                                    let uu____2864
                                                                    =
                                                                    mktac1
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2865
                                                                    =
                                                                    let uu____2868
                                                                    =
                                                                    mktac1
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2869
                                                                    =
                                                                    let uu____2872
                                                                    =
                                                                    mktac1
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2873
                                                                    =
                                                                    let uu____2876
                                                                    =
                                                                    mktac1
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2877
                                                                    =
                                                                    let uu____2880
                                                                    =
                                                                    mktac1
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2881
                                                                    =
                                                                    let uu____2884
                                                                    =
                                                                    mktac1
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2885
                                                                    =
                                                                    let uu____2888
                                                                    =
                                                                    let uu____2889
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac1
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____2889
                                                                     in
                                                                    let uu____2900
                                                                    =
                                                                    let uu____2903
                                                                    =
                                                                    mktac1
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____2904
                                                                    =
                                                                    let uu____2907
                                                                    =
                                                                    mktac1
                                                                    "cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____2908
                                                                    =
                                                                    let uu____2911
                                                                    =
                                                                    mktac1
                                                                    "cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____2912
                                                                    =
                                                                    let uu____2915
                                                                    =
                                                                    mktac1
                                                                    "cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____2916
                                                                    =
                                                                    let uu____2919
                                                                    =
                                                                    mktac1
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                     in
                                                                    let uu____2920
                                                                    =
                                                                    let uu____2923
                                                                    =
                                                                    mktac1
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____2924
                                                                    =
                                                                    let uu____2927
                                                                    =
                                                                    mktac1
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____2928
                                                                    =
                                                                    let uu____2931
                                                                    =
                                                                    mktac1
                                                                    "ngoals"
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____2932
                                                                    =
                                                                    let uu____2935
                                                                    =
                                                                    mktac1
                                                                    "ngoals_smt"
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____2936
                                                                    =
                                                                    let uu____2939
                                                                    =
                                                                    mktac1
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____2940
                                                                    =
                                                                    let uu____2943
                                                                    =
                                                                    let uu____2944
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac2
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____2944
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____2951
                                                                    =
                                                                    let uu____2954
                                                                    =
                                                                    mktac2
                                                                    "unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____2955
                                                                    =
                                                                    let uu____2958
                                                                    =
                                                                    mktac3
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____2959
                                                                    =
                                                                    let uu____2962
                                                                    =
                                                                    mktac2
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                     in
                                                                    let uu____2963
                                                                    =
                                                                    let uu____2966
                                                                    =
                                                                    mktac1
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____2967
                                                                    =
                                                                    let uu____2970
                                                                    =
                                                                    mktac1
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                     in
                                                                    let uu____2971
                                                                    =
                                                                    let uu____2974
                                                                    =
                                                                    mktac1
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    [uu____2974;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____2970
                                                                    ::
                                                                    uu____2971
                                                                     in
                                                                    uu____2966
                                                                    ::
                                                                    uu____2967
                                                                     in
                                                                    uu____2962
                                                                    ::
                                                                    uu____2963
                                                                     in
                                                                    uu____2958
                                                                    ::
                                                                    uu____2959
                                                                     in
                                                                    uu____2954
                                                                    ::
                                                                    uu____2955
                                                                     in
                                                                    uu____2943
                                                                    ::
                                                                    uu____2951
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
                                                                    uu____2907
                                                                    ::
                                                                    uu____2908
                                                                     in
                                                                    uu____2903
                                                                    ::
                                                                    uu____2904
                                                                     in
                                                                    uu____2888
                                                                    ::
                                                                    uu____2900
                                                                     in
                                                                    uu____2884
                                                                    ::
                                                                    uu____2885
                                                                     in
                                                                    uu____2880
                                                                    ::
                                                                    uu____2881
                                                                     in
                                                                    uu____2876
                                                                    ::
                                                                    uu____2877
                                                                     in
                                                                    uu____2872
                                                                    ::
                                                                    uu____2873
                                                                     in
                                                                    uu____2868
                                                                    ::
                                                                    uu____2869
                                                                     in
                                                                    uu____2864
                                                                    ::
                                                                    uu____2865
                                                                     in
                                                                    uu____2860
                                                                    ::
                                                                    uu____2861
                                                                     in
                                                                    uu____2817
                                                                    ::
                                                                    uu____2857
                                                                     in
                                                                    uu____2806
                                                                    ::
                                                                    uu____2814
                                                                     in
                                                                    uu____2802
                                                                    ::
                                                                    uu____2803
                                                                     in
                                                                  uu____2798
                                                                    ::
                                                                    uu____2799
                                                                   in
                                                                uu____2794 ::
                                                                  uu____2795
                                                                 in
                                                              uu____2790 ::
                                                                uu____2791
                                                               in
                                                            uu____2786 ::
                                                              uu____2787
                                                             in
                                                          uu____2782 ::
                                                            uu____2783
                                                           in
                                                        uu____2778 ::
                                                          uu____2779
                                                         in
                                                      uu____2774 ::
                                                        uu____2775
                                                       in
                                                    uu____2770 :: uu____2771
                                                     in
                                                  uu____2766 :: uu____2767
                                                   in
                                                uu____2748 :: uu____2763  in
                                              uu____2715 :: uu____2745  in
                                            uu____2711 :: uu____2712  in
                                          uu____2707 :: uu____2708  in
                                        uu____2703 :: uu____2704  in
                                      uu____2699 :: uu____2700  in
                                    uu____2695 :: uu____2696  in
                                  uu____2691 :: uu____2692  in
                                uu____2687 :: uu____2688  in
                              uu____2683 :: uu____2684  in
                            uu____2679 :: uu____2680  in
                          uu____2675 :: uu____2676  in
                        uu____2671 :: uu____2672  in
                      uu____2667 :: uu____2668  in
                    uu____2656 :: uu____2664  in
                  uu____2645 :: uu____2653  in
                uu____2634 :: uu____2642  in
              uu____2619 :: uu____2631  in
            uu____2615 :: uu____2616  in
          uu____2595 :: uu____2612  in
        uu____2591 :: uu____2592  in
      uu____2585 :: uu____2588  in
    FStar_List.append uu____2582
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
               let uu____2997 =
                 let uu____3002 =
                   let uu____3003 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____3003]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____3002  in
               uu____2997 FStar_Pervasives_Native.None rng  in
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
             let uu____3044 =
               let uu____3049 =
                 let uu____3050 =
                   let uu____3057 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____3057  in
                 [uu____3050]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3049  in
             uu____3044 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____3076 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____3076
            then
              let uu____3077 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____3077
            else ());
           (let result =
              let uu____3080 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____3080 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____3084 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____3084
             then
               let uu____3085 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____3085
             else ());
            (let res =
               let uu____3092 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Syntax_Embeddings.unembed uu____3092 result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____3105 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3105
                   (fun uu____3109  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____3114 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3114
                   (fun uu____3118  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____3121 =
                   let uu____3126 =
                     let uu____3127 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____3127
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____3126)  in
                 FStar_Errors.raise_error uu____3121
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      let uu____3134 = unembed_tactic_0 eb embedded_tac_b  in
      FStar_All.pipe_left (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
        uu____3134

let (report_implicits :
  FStar_Tactics_Types.proofstate -> FStar_TypeChecker_Env.implicits -> unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____3187  ->
             match uu____3187 with
             | (r,ty,uv,rng,uu____3208) ->
                 let uu____3209 =
                   let uu____3210 =
                     FStar_Syntax_Print.uvar_to_string
                       uv.FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   let uu____3211 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____3210 uu____3211 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____3209, rng)) is
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
        (let uu____3266 = FStar_ST.op_Bang tacdbg  in
         if uu____3266
         then
           let uu____3290 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____3290
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____3294 = FStar_ST.op_Bang tacdbg  in
          if uu____3294
          then
            let uu____3318 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____3318
          else ());
         (let uu____3320 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____3320 with
          | (uu____3333,uu____3334,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic1  in
                let uu____3341 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____3341 with
                | (env1,uu____3355) ->
                    let env2 =
                      let uu___62_3361 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___62_3361.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___62_3361.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___62_3361.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___62_3361.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___62_3361.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___62_3361.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___62_3361.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___62_3361.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___62_3361.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___62_3361.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___62_3361.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___62_3361.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___62_3361.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___62_3361.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___62_3361.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___62_3361.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___62_3361.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___62_3361.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___62_3361.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___62_3361.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___62_3361.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___62_3361.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___62_3361.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___62_3361.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___62_3361.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___62_3361.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___62_3361.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___62_3361.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___62_3361.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___62_3361.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___62_3361.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___62_3361.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___62_3361.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___62_3361.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___62_3361.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___62_3361.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___62_3361.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let env3 =
                      let uu___63_3363 = env2  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___63_3363.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___63_3363.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___63_3363.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___63_3363.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___63_3363.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___63_3363.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___63_3363.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___63_3363.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___63_3363.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___63_3363.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___63_3363.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___63_3363.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___63_3363.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___63_3363.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___63_3363.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___63_3363.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___63_3363.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___63_3363.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___63_3363.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___63_3363.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes = true;
                        FStar_TypeChecker_Env.failhard =
                          (uu___63_3363.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___63_3363.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___63_3363.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___63_3363.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___63_3363.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___63_3363.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___63_3363.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___63_3363.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___63_3363.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___63_3363.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___63_3363.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___63_3363.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___63_3363.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___63_3363.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___63_3363.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___63_3363.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___63_3363.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____3364 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ  in
                    (match uu____3364 with
                     | (ps,w) ->
                         ((let uu____3378 = FStar_ST.op_Bang tacdbg  in
                           if uu____3378
                           then
                             let uu____3402 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____3402
                           else ());
                          (let uu____3404 =
                             FStar_Util.record_time
                               (fun uu____3414  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____3404 with
                           | (res,ms) ->
                               ((let uu____3428 = FStar_ST.op_Bang tacdbg  in
                                 if uu____3428
                                 then
                                   let uu____3452 =
                                     FStar_Syntax_Print.term_to_string
                                       tactic1
                                      in
                                   let uu____3453 =
                                     FStar_Util.string_of_int ms  in
                                   let uu____3454 =
                                     FStar_Syntax_Print.lid_to_string
                                       env3.FStar_TypeChecker_Env.curmodule
                                      in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____3452 uu____3453 uu____3454
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____3462,ps1) ->
                                     ((let uu____3465 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____3465
                                       then
                                         let uu____3489 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____3489
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____3496 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____3496
                                           then
                                             let uu____3497 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____3497
                                              then ()
                                              else
                                                (let uu____3499 =
                                                   let uu____3500 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____3500
                                                    in
                                                 failwith uu____3499))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___64_3503 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___64_3503.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___64_3503.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___64_3503.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____3505 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env3 g1
                                            in
                                         FStar_All.pipe_right uu____3505
                                           (FStar_TypeChecker_Rel.resolve_implicits_tac
                                              env3)
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____3512 =
                                         let uu____3513 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____3513 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____3512 "at the time of failure");
                                      (let uu____3514 =
                                         let uu____3519 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____3519)
                                          in
                                       FStar_Errors.raise_error uu____3514
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____3531 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____3537 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____3543 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3598 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3638 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3692 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3733 . 'Auu____3733 -> 'Auu____3733 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3761 = FStar_Syntax_Util.head_and_args t  in
        match uu____3761 with
        | (hd1,args) ->
            let uu____3798 =
              let uu____3813 =
                let uu____3814 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3814.FStar_Syntax_Syntax.n  in
              (uu____3813, args)  in
            (match uu____3798 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3829))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3892 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3892 with
                       | (gs,uu____3900) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3907 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3907 with
                       | (gs,uu____3915) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3958 =
                        let uu____3965 =
                          let uu____3968 =
                            let uu____3969 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3969
                             in
                          [uu____3968]  in
                        (FStar_Syntax_Util.t_true, uu____3965)  in
                      Simplified uu____3958
                  | Both  ->
                      let uu____3980 =
                        let uu____3989 =
                          let uu____3992 =
                            let uu____3993 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3993
                             in
                          [uu____3992]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3989)  in
                      Dual uu____3980
                  | Neg  -> Simplified (assertion, []))
             | uu____4006 -> Unchanged t)
  
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
    fun uu___61_4096  ->
      match uu___61_4096 with
      | Unchanged t -> let uu____4102 = f t  in Unchanged uu____4102
      | Simplified (t,gs) ->
          let uu____4109 = let uu____4116 = f t  in (uu____4116, gs)  in
          Simplified uu____4109
      | Dual (tn,tp,gs) ->
          let uu____4126 =
            let uu____4135 = f tn  in
            let uu____4136 = f tp  in (uu____4135, uu____4136, gs)  in
          Dual uu____4126
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____4199 = f t1 t2  in Unchanged uu____4199
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____4211 = let uu____4218 = f t1 t2  in (uu____4218, gs)
               in
            Simplified uu____4211
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____4232 = let uu____4239 = f t1 t2  in (uu____4239, gs)
               in
            Simplified uu____4232
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____4258 =
              let uu____4265 = f t1 t2  in
              (uu____4265, (FStar_List.append gs1 gs2))  in
            Simplified uu____4258
        | uu____4268 ->
            let uu____4277 = explode x  in
            (match uu____4277 with
             | (n1,p1,gs1) ->
                 let uu____4295 = explode y  in
                 (match uu____4295 with
                  | (n2,p2,gs2) ->
                      let uu____4313 =
                        let uu____4322 = f n1 n2  in
                        let uu____4323 = f p1 p2  in
                        (uu____4322, uu____4323, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____4313))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____4395 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____4395
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____4443  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____4485 =
              let uu____4486 = FStar_Syntax_Subst.compress t  in
              uu____4486.FStar_Syntax_Syntax.n  in
            match uu____4485 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____4498 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____4498 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____4524 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____4524 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4544;
                   FStar_Syntax_Syntax.vars = uu____4545;_},(p,uu____4547)::
                 (q,uu____4549)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____4589 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4589
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____4592 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____4592 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4606 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4606.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4610;
                   FStar_Syntax_Syntax.vars = uu____4611;_},(p,uu____4613)::
                 (q,uu____4615)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4655 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4655
                   in
                let xq =
                  let uu____4657 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4657
                   in
                let r1 =
                  let uu____4659 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4659 p  in
                let r2 =
                  let uu____4661 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4661 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4668,Unchanged uu____4669) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4687 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4687.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4690 ->
                     let uu____4699 = explode r1  in
                     (match uu____4699 with
                      | (pn,pp,gs1) ->
                          let uu____4717 = explode r2  in
                          (match uu____4717 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4738 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4741 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4738
                                   uu____4741
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4795  ->
                       fun r  ->
                         match uu____4795 with
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
                let uu____4913 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4913 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4947  ->
                            match uu____4947 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4961 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___65_4987 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___65_4987.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___65_4987.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4961 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____5011 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____5011.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____5057 = traverse f pol e t1  in
                let uu____5062 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____5062 uu____5057
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___66_5102 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___66_5102.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___66_5102.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____5109 =
                f pol e
                  (let uu___67_5113 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___67_5113.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___67_5113.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____5109
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___68_5123 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___68_5123.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___68_5123.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____5124 = explode rp  in
              (match uu____5124 with
               | (uu____5133,p',gs') ->
                   Dual
                     ((let uu___69_5143 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___69_5143.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___69_5143.FStar_Syntax_Syntax.vars)
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
      (let uu____5186 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5186);
      (let uu____5211 = FStar_ST.op_Bang tacdbg  in
       if uu____5211
       then
         let uu____5235 =
           let uu____5236 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____5236
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____5237 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____5235
           uu____5237
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____5266 =
         let uu____5273 = traverse by_tactic_interp Pos env goal  in
         match uu____5273 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____5291 -> failwith "no"  in
       match uu____5266 with
       | (t',gs) ->
           ((let uu____5313 = FStar_ST.op_Bang tacdbg  in
             if uu____5313
             then
               let uu____5337 =
                 let uu____5338 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____5338
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____5339 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____5337 uu____5339
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5386  ->
                    fun g  ->
                      match uu____5386 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5431 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____5431 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5434 =
                                  let uu____5439 =
                                    let uu____5440 =
                                      FStar_Syntax_Print.term_to_string
                                        g.FStar_Tactics_Types.goal_ty
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5440
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5439)
                                   in
                                FStar_Errors.raise_error uu____5434
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5443 = FStar_ST.op_Bang tacdbg  in
                            if uu____5443
                            then
                              let uu____5467 = FStar_Util.string_of_int n1
                                 in
                              let uu____5468 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5467 uu____5468
                            else ());
                           (let gt' =
                              let uu____5471 =
                                let uu____5472 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____5472
                                 in
                              FStar_TypeChecker_Util.label uu____5471
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____5487 = s1  in
             match uu____5487 with
             | (uu____5508,gs1) ->
                 let uu____5526 =
                   let uu____5533 = FStar_Options.peek ()  in
                   (env, t', uu____5533)  in
                 uu____5526 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____5546 =
        let uu____5547 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____5547  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____5546 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____5548 =
      let uu____5553 =
        let uu____5554 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____5561 =
          let uu____5570 = FStar_Syntax_Syntax.as_arg a  in [uu____5570]  in
        uu____5554 :: uu____5561  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____5553  in
    uu____5548 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____5613 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____5613);
        (let uu____5637 =
           let uu____5644 = reify_tactic tau  in
           run_tactic_on_typ uu____5644 env typ  in
         match uu____5637 with
         | (gs,w) ->
             let uu____5651 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5655 =
                      let uu____5656 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5656  in
                    Prims.op_Negation uu____5655) gs
                in
             if uu____5651
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
      (let uu____5675 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5675);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____5700 =
         let uu____5707 = reify_tactic tau  in
         run_tactic_on_typ uu____5707 env typ  in
       match uu____5700 with
       | (gs,w) ->
           ((let uu____5717 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5721 =
                      let uu____5722 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5722  in
                    Prims.op_Negation uu____5721) gs
                in
             if uu____5717
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
             let uu____5727 =
               let uu____5732 =
                 FStar_Syntax_Embeddings.e_list
                   FStar_Reflection_Embeddings.e_sigelt
                  in
               FStar_Syntax_Embeddings.unembed uu____5732 w1  in
             FStar_All.pipe_left FStar_Util.must uu____5727)))
  