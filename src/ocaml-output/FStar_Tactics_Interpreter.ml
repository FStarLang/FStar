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
                  let uu____95 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Tactics_Embedding.e_proofstate embedded_state
                     in
                  FStar_Util.bind_opt uu____95
                    (fun ps  ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       FStar_Tactics_Basic.log ps1
                         (fun uu____108  ->
                            let uu____109 = FStar_Ident.string_of_lid nm  in
                            let uu____110 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____109 uu____110);
                       (let res =
                          let uu____112 = FStar_Tactics_Embedding.e_result er
                             in
                          let uu____117 =
                            FStar_TypeChecker_Normalize.psc_range psc  in
                          let uu____118 = FStar_Tactics_Basic.run_safe t ps1
                             in
                          FStar_Syntax_Embeddings.embed uu____112 uu____117
                            uu____118
                           in
                        FStar_Pervasives_Native.Some res))
              | uu____123 ->
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
                | (a,uu____201)::(embedded_state,uu____203)::[] ->
                    let uu____244 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state
                       in
                    FStar_Util.bind_opt uu____244
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____257  ->
                              let uu____258 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____259 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____258 uu____259);
                         (let uu____260 =
                            FStar_Syntax_Embeddings.unembed ea a  in
                          FStar_Util.bind_opt uu____260
                            (fun a1  ->
                               let res =
                                 let uu____270 = t a1  in
                                 FStar_Tactics_Basic.run_safe uu____270 ps1
                                  in
                               let uu____273 =
                                 let uu____274 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____279 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 FStar_Syntax_Embeddings.embed uu____274
                                   uu____279 res
                                  in
                               FStar_Pervasives_Native.Some uu____273)))
                | uu____282 ->
                    let uu____283 =
                      let uu____284 = FStar_Ident.string_of_lid nm  in
                      let uu____285 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____284 uu____285
                       in
                    failwith uu____283
  
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
                | (a,uu____368)::(embedded_state,uu____370)::[] ->
                    let uu____411 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state
                       in
                    FStar_Util.bind_opt uu____411
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____424  ->
                              let uu____425 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____426 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____425 uu____426);
                         (let uu____427 =
                            FStar_Syntax_Embeddings.unembed ea a  in
                          FStar_Util.bind_opt uu____427
                            (fun a1  ->
                               let res =
                                 let uu____437 = t psc a1  in
                                 FStar_Tactics_Basic.run_safe uu____437 ps1
                                  in
                               let uu____440 =
                                 let uu____441 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____446 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 FStar_Syntax_Embeddings.embed uu____441
                                   uu____446 res
                                  in
                               FStar_Pervasives_Native.Some uu____440)))
                | uu____449 ->
                    let uu____450 =
                      let uu____451 = FStar_Ident.string_of_lid nm  in
                      let uu____452 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____451 uu____452
                       in
                    failwith uu____450
  
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
                  | (a,uu____549)::(b,uu____551)::(embedded_state,uu____553)::[]
                      ->
                      let uu____610 =
                        FStar_Syntax_Embeddings.unembed
                          FStar_Tactics_Embedding.e_proofstate embedded_state
                         in
                      FStar_Util.bind_opt uu____610
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____623  ->
                                let uu____624 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____625 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____624
                                  uu____625);
                           (let uu____626 =
                              FStar_Syntax_Embeddings.unembed ea a  in
                            FStar_Util.bind_opt uu____626
                              (fun a1  ->
                                 let uu____632 =
                                   FStar_Syntax_Embeddings.unembed eb b  in
                                 FStar_Util.bind_opt uu____632
                                   (fun b1  ->
                                      let res =
                                        let uu____642 = t a1 b1  in
                                        FStar_Tactics_Basic.run_safe
                                          uu____642 ps1
                                         in
                                      let uu____645 =
                                        let uu____646 =
                                          FStar_Tactics_Embedding.e_result er
                                           in
                                        let uu____651 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc
                                           in
                                        FStar_Syntax_Embeddings.embed
                                          uu____646 uu____651 res
                                         in
                                      FStar_Pervasives_Native.Some uu____645))))
                  | uu____654 ->
                      let uu____655 =
                        let uu____656 = FStar_Ident.string_of_lid nm  in
                        let uu____657 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____656 uu____657
                         in
                      failwith uu____655
  
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
                    | (a,uu____773)::(b,uu____775)::(c,uu____777)::(embedded_state,uu____779)::[]
                        ->
                        let uu____852 =
                          FStar_Syntax_Embeddings.unembed
                            FStar_Tactics_Embedding.e_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____852
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____865  ->
                                  let uu____866 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____867 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____866
                                    uu____867);
                             (let uu____868 =
                                FStar_Syntax_Embeddings.unembed ea a  in
                              FStar_Util.bind_opt uu____868
                                (fun a1  ->
                                   let uu____874 =
                                     FStar_Syntax_Embeddings.unembed eb b  in
                                   FStar_Util.bind_opt uu____874
                                     (fun b1  ->
                                        let uu____880 =
                                          FStar_Syntax_Embeddings.unembed ec
                                            c
                                           in
                                        FStar_Util.bind_opt uu____880
                                          (fun c1  ->
                                             let res =
                                               let uu____890 = t a1 b1 c1  in
                                               FStar_Tactics_Basic.run_safe
                                                 uu____890 ps1
                                                in
                                             let uu____893 =
                                               let uu____894 =
                                                 FStar_Tactics_Embedding.e_result
                                                   er
                                                  in
                                               let uu____899 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc
                                                  in
                                               FStar_Syntax_Embeddings.embed
                                                 uu____894 uu____899 res
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____893)))))
                    | uu____902 ->
                        let uu____903 =
                          let uu____904 = FStar_Ident.string_of_lid nm  in
                          let uu____905 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____904 uu____905
                           in
                        failwith uu____903
  
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
                      | (a,uu____1040)::(b,uu____1042)::(c,uu____1044)::
                          (d,uu____1046)::(embedded_state,uu____1048)::[] ->
                          let uu____1137 =
                            FStar_Syntax_Embeddings.unembed
                              FStar_Tactics_Embedding.e_proofstate
                              embedded_state
                             in
                          FStar_Util.bind_opt uu____1137
                            (fun ps  ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____1150  ->
                                    let uu____1151 =
                                      FStar_Ident.string_of_lid nm  in
                                    let uu____1152 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state
                                       in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n"
                                      uu____1151 uu____1152);
                               (let uu____1153 =
                                  FStar_Syntax_Embeddings.unembed ea a  in
                                FStar_Util.bind_opt uu____1153
                                  (fun a1  ->
                                     let uu____1159 =
                                       FStar_Syntax_Embeddings.unembed eb b
                                        in
                                     FStar_Util.bind_opt uu____1159
                                       (fun b1  ->
                                          let uu____1165 =
                                            FStar_Syntax_Embeddings.unembed
                                              ec c
                                             in
                                          FStar_Util.bind_opt uu____1165
                                            (fun c1  ->
                                               let uu____1171 =
                                                 FStar_Syntax_Embeddings.unembed
                                                   ed d
                                                  in
                                               FStar_Util.bind_opt uu____1171
                                                 (fun d1  ->
                                                    let res =
                                                      let uu____1181 =
                                                        t a1 b1 c1 d1  in
                                                      FStar_Tactics_Basic.run_safe
                                                        uu____1181 ps1
                                                       in
                                                    let uu____1184 =
                                                      let uu____1185 =
                                                        FStar_Tactics_Embedding.e_result
                                                          er
                                                         in
                                                      let uu____1190 =
                                                        FStar_TypeChecker_Normalize.psc_range
                                                          psc
                                                         in
                                                      FStar_Syntax_Embeddings.embed
                                                        uu____1185 uu____1190
                                                        res
                                                       in
                                                    FStar_Pervasives_Native.Some
                                                      uu____1184))))))
                      | uu____1193 ->
                          let uu____1194 =
                            let uu____1195 = FStar_Ident.string_of_lid nm  in
                            let uu____1196 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____1195 uu____1196
                             in
                          failwith uu____1194
  
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
                        | (a,uu____1350)::(b,uu____1352)::(c,uu____1354)::
                            (d,uu____1356)::(e,uu____1358)::(embedded_state,uu____1360)::[]
                            ->
                            let uu____1465 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Tactics_Embedding.e_proofstate
                                embedded_state
                               in
                            FStar_Util.bind_opt uu____1465
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1478  ->
                                      let uu____1479 =
                                        FStar_Ident.string_of_lid nm  in
                                      let uu____1480 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state
                                         in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1479 uu____1480);
                                 (let uu____1481 =
                                    FStar_Syntax_Embeddings.unembed ea a  in
                                  FStar_Util.bind_opt uu____1481
                                    (fun a1  ->
                                       let uu____1487 =
                                         FStar_Syntax_Embeddings.unembed eb b
                                          in
                                       FStar_Util.bind_opt uu____1487
                                         (fun b1  ->
                                            let uu____1493 =
                                              FStar_Syntax_Embeddings.unembed
                                                ec c
                                               in
                                            FStar_Util.bind_opt uu____1493
                                              (fun c1  ->
                                                 let uu____1499 =
                                                   FStar_Syntax_Embeddings.unembed
                                                     ed d
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____1499
                                                   (fun d1  ->
                                                      let uu____1505 =
                                                        FStar_Syntax_Embeddings.unembed
                                                          ee e
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____1505
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____1515 =
                                                               t a1 b1 c1 d1
                                                                 e1
                                                                in
                                                             FStar_Tactics_Basic.run_safe
                                                               uu____1515 ps1
                                                              in
                                                           let uu____1518 =
                                                             let uu____1519 =
                                                               FStar_Tactics_Embedding.e_result
                                                                 er
                                                                in
                                                             let uu____1524 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc
                                                                in
                                                             FStar_Syntax_Embeddings.embed
                                                               uu____1519
                                                               uu____1524 res
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1518)))))))
                        | uu____1527 ->
                            let uu____1528 =
                              let uu____1529 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____1530 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1529 uu____1530
                               in
                            failwith uu____1528
  
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
                          | (a,uu____1703)::(b,uu____1705)::(c,uu____1707)::
                              (d,uu____1709)::(e,uu____1711)::(f,uu____1713)::
                              (embedded_state,uu____1715)::[] ->
                              let uu____1836 =
                                FStar_Syntax_Embeddings.unembed
                                  FStar_Tactics_Embedding.e_proofstate
                                  embedded_state
                                 in
                              FStar_Util.bind_opt uu____1836
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1849  ->
                                        let uu____1850 =
                                          FStar_Ident.string_of_lid nm  in
                                        let uu____1851 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state
                                           in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1850 uu____1851);
                                   (let uu____1852 =
                                      FStar_Syntax_Embeddings.unembed ea a
                                       in
                                    FStar_Util.bind_opt uu____1852
                                      (fun a1  ->
                                         let uu____1858 =
                                           FStar_Syntax_Embeddings.unembed eb
                                             b
                                            in
                                         FStar_Util.bind_opt uu____1858
                                           (fun b1  ->
                                              let uu____1864 =
                                                FStar_Syntax_Embeddings.unembed
                                                  ec c
                                                 in
                                              FStar_Util.bind_opt uu____1864
                                                (fun c1  ->
                                                   let uu____1870 =
                                                     FStar_Syntax_Embeddings.unembed
                                                       ed d
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____1870
                                                     (fun d1  ->
                                                        let uu____1876 =
                                                          FStar_Syntax_Embeddings.unembed
                                                            ee e
                                                           in
                                                        FStar_Util.bind_opt
                                                          uu____1876
                                                          (fun e1  ->
                                                             let uu____1882 =
                                                               FStar_Syntax_Embeddings.unembed
                                                                 ef f
                                                                in
                                                             FStar_Util.bind_opt
                                                               uu____1882
                                                               (fun f1  ->
                                                                  let res =
                                                                    let uu____1892
                                                                    =
                                                                    t a1 b1
                                                                    c1 d1 e1
                                                                    f1  in
                                                                    FStar_Tactics_Basic.run_safe
                                                                    uu____1892
                                                                    ps1  in
                                                                  let uu____1895
                                                                    =
                                                                    let uu____1896
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                    let uu____1901
                                                                    =
                                                                    FStar_TypeChecker_Normalize.psc_range
                                                                    psc  in
                                                                    FStar_Syntax_Embeddings.embed
                                                                    uu____1896
                                                                    uu____1901
                                                                    res  in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____1895))))))))
                          | uu____1904 ->
                              let uu____1905 =
                                let uu____1906 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____1907 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1906 uu____1907
                                 in
                              failwith uu____1905
  
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
        't1 FStar_Syntax_Embeddings.embedding ->
          't2 FStar_Syntax_Embeddings.embedding ->
            't3 FStar_Syntax_Embeddings.embedding ->
              't4 FStar_Syntax_Embeddings.embedding ->
                't5 FStar_Syntax_Embeddings.embedding ->
                  't6 FStar_Syntax_Embeddings.embedding ->
                    't7 FStar_Syntax_Embeddings.embedding ->
                      't8 FStar_Syntax_Embeddings.embedding ->
                        't9 FStar_Syntax_Embeddings.embedding ->
                          't10 FStar_Syntax_Embeddings.embedding ->
                            't11 FStar_Syntax_Embeddings.embedding ->
                              't12 FStar_Syntax_Embeddings.embedding ->
                                't13 FStar_Syntax_Embeddings.embedding ->
                                  'r FStar_Syntax_Embeddings.embedding ->
                                    FStar_Ident.lid ->
                                      FStar_TypeChecker_Normalize.psc ->
                                        FStar_Syntax_Syntax.args ->
                                          FStar_Syntax_Syntax.term
                                            FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun e_t1  ->
        fun e_t2  ->
          fun e_t3  ->
            fun e_t4  ->
              fun e_t5  ->
                fun e_t6  ->
                  fun e_t7  ->
                    fun e_t8  ->
                      fun e_t9  ->
                        fun e_t10  ->
                          fun e_t11  ->
                            fun e_t12  ->
                              fun e_t13  ->
                                fun er  ->
                                  fun nm  ->
                                    fun psc  ->
                                      fun args  ->
                                        match args with
                                        | (a1,uu____2213)::(a2,uu____2215)::
                                            (a3,uu____2217)::(a4,uu____2219)::
                                            (a5,uu____2221)::(a6,uu____2223)::
                                            (a7,uu____2225)::(a8,uu____2227)::
                                            (a9,uu____2229)::(a10,uu____2231)::
                                            (a11,uu____2233)::(a12,uu____2235)::
                                            (a13,uu____2237)::(embedded_state,uu____2239)::[]
                                            ->
                                            let uu____2472 =
                                              FStar_Syntax_Embeddings.unembed
                                                FStar_Tactics_Embedding.e_proofstate
                                                embedded_state
                                               in
                                            FStar_Util.bind_opt uu____2472
                                              (fun ps  ->
                                                 let ps1 =
                                                   FStar_Tactics_Types.set_ps_psc
                                                     psc ps
                                                    in
                                                 FStar_Tactics_Basic.log ps1
                                                   (fun uu____2485  ->
                                                      let uu____2486 =
                                                        FStar_Ident.string_of_lid
                                                          nm
                                                         in
                                                      let uu____2487 =
                                                        FStar_Syntax_Print.term_to_string
                                                          embedded_state
                                                         in
                                                      FStar_Util.print2
                                                        "Reached %s, goals are: %s\n"
                                                        uu____2486 uu____2487);
                                                 (let uu____2488 =
                                                    FStar_Syntax_Embeddings.unembed
                                                      e_t1 a1
                                                     in
                                                  FStar_Util.bind_opt
                                                    uu____2488
                                                    (fun a14  ->
                                                       let uu____2494 =
                                                         FStar_Syntax_Embeddings.unembed
                                                           e_t2 a2
                                                          in
                                                       FStar_Util.bind_opt
                                                         uu____2494
                                                         (fun a21  ->
                                                            let uu____2500 =
                                                              FStar_Syntax_Embeddings.unembed
                                                                e_t3 a3
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____2500
                                                              (fun a31  ->
                                                                 let uu____2506
                                                                   =
                                                                   FStar_Syntax_Embeddings.unembed
                                                                    e_t4 a4
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____2506
                                                                   (fun a41 
                                                                    ->
                                                                    let uu____2512
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed
                                                                    e_t5 a5
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____2512
                                                                    (fun a51 
                                                                    ->
                                                                    let uu____2518
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed
                                                                    e_t6 a6
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____2518
                                                                    (fun a61 
                                                                    ->
                                                                    let uu____2524
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed
                                                                    e_t7 a7
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____2524
                                                                    (fun a71 
                                                                    ->
                                                                    let uu____2530
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed
                                                                    e_t8 a8
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____2530
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____2536
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed
                                                                    e_t9 a9
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____2536
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____2542
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed
                                                                    e_t10 a10
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____2542
                                                                    (fun a101
                                                                     ->
                                                                    let uu____2548
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed
                                                                    e_t11 a11
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____2548
                                                                    (fun a111
                                                                     ->
                                                                    let uu____2554
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed
                                                                    e_t12 a12
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____2554
                                                                    (fun a121
                                                                     ->
                                                                    let uu____2560
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed
                                                                    e_t13 a13
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____2560
                                                                    (fun a131
                                                                     ->
                                                                    let res =
                                                                    let uu____2570
                                                                    =
                                                                    t a14 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131  in
                                                                    FStar_Tactics_Basic.run
                                                                    uu____2570
                                                                    ps1  in
                                                                    let uu____2573
                                                                    =
                                                                    let uu____2574
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                    let uu____2579
                                                                    =
                                                                    FStar_TypeChecker_Normalize.psc_range
                                                                    psc  in
                                                                    FStar_Syntax_Embeddings.embed
                                                                    uu____2574
                                                                    uu____2579
                                                                    res  in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____2573)))))))))))))))
                                        | uu____2582 ->
                                            let uu____2583 =
                                              let uu____2584 =
                                                FStar_Ident.string_of_lid nm
                                                 in
                                              let uu____2585 =
                                                FStar_Syntax_Print.args_to_string
                                                  args
                                                 in
                                              FStar_Util.format2
                                                "Unexpected application of tactic primitive %s %s"
                                                uu____2584 uu____2585
                                               in
                                            failwith uu____2583
  
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
      (fun uu____2729  ->
         fun uu____2730  -> failwith "Impossible: embedding tactic (0)?")
      (fun w  ->
         fun t  ->
           let uu____2738 = unembed_tactic_0 er t  in
           FStar_All.pipe_left
             (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____2738)
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
        (fun uu____2762  ->
           fun uu____2763  -> failwith "Impossible: embedding tactic (1)?")
        (fun w  -> fun t  -> unembed_tactic_1 ea er t)
        FStar_Syntax_Syntax.t_unit

and (primitive_steps :
  unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____2772  ->
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
      | (ps,uu____3178)::[] ->
          let uu____3203 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____3203
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____3211 =
                 let uu____3212 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____3213 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____3212 uu____3213
                  in
               FStar_Pervasives_Native.Some uu____3211)
      | uu____3214 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____3218 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____3218;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____3235)::[] ->
          let uu____3260 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____3260
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____3268 =
                 let uu____3269 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____3270 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____3269 uu____3270
                  in
               FStar_Pervasives_Native.Some uu____3268)
      | uu____3271 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____3275 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____3275;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____3292)::[] ->
          let uu____3317 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____3317
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____3326 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____3345)::(r,uu____3347)::[] ->
          let uu____3388 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____3388
            (fun ps1  ->
               let uu____3394 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_range r
                  in
               FStar_Util.bind_opt uu____3394
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____3402 =
                      let uu____3403 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Syntax_Embeddings.embed
                        FStar_Tactics_Embedding.e_proofstate uu____3403 ps'
                       in
                    FStar_Pervasives_Native.Some uu____3402))
      | uu____3404 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____3423)::(b,uu____3425)::[] ->
          let uu____3466 =
            FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_env
              env_t
             in
          FStar_Util.bind_opt uu____3466
            (fun env  ->
               let uu____3472 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Reflection_Embeddings.e_binder b
                  in
               FStar_Util.bind_opt uu____3472
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____3492 =
                      FStar_Syntax_Embeddings.embed
                        FStar_Reflection_Embeddings.e_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____3492))
      | uu____3493 -> failwith "Unexpected application of push_binder"  in
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
    let uu____3502 =
      let uu____3505 =
        mktac2 "fail" (fun uu____3507  -> FStar_Tactics_Basic.fail)
          FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string
          FStar_Syntax_Embeddings.e_any
         in
      let uu____3508 =
        let uu____3511 =
          mktac1 "trivial" FStar_Tactics_Basic.trivial
            FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
           in
        let uu____3512 =
          let uu____3515 =
            let uu____3516 = e_tactic_0' FStar_Syntax_Embeddings.e_any  in
            let uu____3521 =
              FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any
               in
            mktac2 "__trytac" (fun uu____3531  -> FStar_Tactics_Basic.trytac)
              FStar_Syntax_Embeddings.e_any uu____3516 uu____3521
             in
          let uu____3532 =
            let uu____3535 =
              mktac1 "intro" FStar_Tactics_Basic.intro
                FStar_Syntax_Embeddings.e_unit
                FStar_Reflection_Embeddings.e_binder
               in
            let uu____3536 =
              let uu____3539 =
                let uu____3540 =
                  FStar_Syntax_Embeddings.e_tuple2
                    FStar_Reflection_Embeddings.e_binder
                    FStar_Reflection_Embeddings.e_binder
                   in
                mktac1 "intro_rec" FStar_Tactics_Basic.intro_rec
                  FStar_Syntax_Embeddings.e_unit uu____3540
                 in
              let uu____3551 =
                let uu____3554 =
                  let uu____3555 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Syntax_Embeddings.e_norm_step
                     in
                  mktac1 "norm" FStar_Tactics_Basic.norm uu____3555
                    FStar_Syntax_Embeddings.e_unit
                   in
                let uu____3562 =
                  let uu____3565 =
                    let uu____3566 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_norm_step
                       in
                    mktac3 "norm_term_env" FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Embeddings.e_env uu____3566
                      FStar_Reflection_Embeddings.e_term
                      FStar_Reflection_Embeddings.e_term
                     in
                  let uu____3573 =
                    let uu____3576 =
                      let uu____3577 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step
                         in
                      mktac2 "norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____3577
                        FStar_Reflection_Embeddings.e_binder
                        FStar_Syntax_Embeddings.e_unit
                       in
                    let uu____3584 =
                      let uu____3587 =
                        mktac2 "rename_to" FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_string
                          FStar_Syntax_Embeddings.e_unit
                         in
                      let uu____3588 =
                        let uu____3591 =
                          mktac1 "binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_unit
                           in
                        let uu____3592 =
                          let uu____3595 =
                            mktac1 "revert" FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Syntax_Embeddings.e_unit
                             in
                          let uu____3596 =
                            let uu____3599 =
                              mktac1 "clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit
                               in
                            let uu____3600 =
                              let uu____3603 =
                                mktac1 "clear" FStar_Tactics_Basic.clear
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                 in
                              let uu____3604 =
                                let uu____3607 =
                                  mktac1 "rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_unit
                                   in
                                let uu____3608 =
                                  let uu____3611 =
                                    mktac1 "smt" FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                     in
                                  let uu____3612 =
                                    let uu____3615 =
                                      mktac1 "refine_intro"
                                        FStar_Tactics_Basic.refine_intro
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                       in
                                    let uu____3616 =
                                      let uu____3619 =
                                        mktac2 "t_exact"
                                          FStar_Tactics_Basic.t_exact
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Syntax_Embeddings.e_unit
                                         in
                                      let uu____3620 =
                                        let uu____3623 =
                                          mktac1 "apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_unit
                                           in
                                        let uu____3624 =
                                          let uu____3627 =
                                            mktac1 "apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Embeddings.e_term
                                              FStar_Syntax_Embeddings.e_unit
                                             in
                                          let uu____3628 =
                                            let uu____3631 =
                                              mktac1 "apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Syntax_Embeddings.e_unit
                                               in
                                            let uu____3632 =
                                              let uu____3635 =
                                                let uu____3636 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____3641 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____3646 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Syntax_Embeddings.e_any
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                mktac5 "__divide"
                                                  (fun uu____3663  ->
                                                     fun uu____3664  ->
                                                       FStar_Tactics_Basic.divide)
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_int
                                                  uu____3636 uu____3641
                                                  uu____3646
                                                 in
                                              let uu____3665 =
                                                let uu____3668 =
                                                  let uu____3669 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____3674 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  mktac2 "__seq"
                                                    FStar_Tactics_Basic.seq
                                                    uu____3669 uu____3674
                                                    FStar_Syntax_Embeddings.e_unit
                                                   in
                                                let uu____3683 =
                                                  let uu____3686 =
                                                    mktac1 "set_options"
                                                      FStar_Tactics_Basic.set_options
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____3687 =
                                                    let uu____3690 =
                                                      mktac1 "tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Reflection_Embeddings.e_term
                                                       in
                                                    let uu____3691 =
                                                      let uu____3694 =
                                                        mktac1 "unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_unit
                                                         in
                                                      let uu____3695 =
                                                        let uu____3698 =
                                                          mktac2 "unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Reflection_Embeddings.e_term
                                                            FStar_Syntax_Embeddings.e_any
                                                           in
                                                        let uu____3699 =
                                                          let uu____3702 =
                                                            mktac1 "prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.e_string
                                                              FStar_Syntax_Embeddings.e_unit
                                                             in
                                                          let uu____3703 =
                                                            let uu____3706 =
                                                              mktac1 "addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____3707 =
                                                              let uu____3710
                                                                =
                                                                mktac1
                                                                  "print"
                                                                  FStar_Tactics_Basic.print
                                                                  FStar_Syntax_Embeddings.e_string
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                 in
                                                              let uu____3711
                                                                =
                                                                let uu____3714
                                                                  =
                                                                  mktac1
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                   in
                                                                let uu____3715
                                                                  =
                                                                  let uu____3718
                                                                    =
                                                                    mktac1
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                  let uu____3719
                                                                    =
                                                                    let uu____3722
                                                                    =
                                                                    mktac1
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3723
                                                                    =
                                                                    let uu____3726
                                                                    =
                                                                    let uu____3727
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____3727
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3734
                                                                    =
                                                                    let uu____3737
                                                                    =
                                                                    let uu____3738
                                                                    =
                                                                    let uu____3750
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____3750
                                                                     in
                                                                    let uu____3761
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____3738
                                                                    uu____3761
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3777
                                                                    =
                                                                    let uu____3780
                                                                    =
                                                                    mktac1
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3781
                                                                    =
                                                                    let uu____3784
                                                                    =
                                                                    mktac1
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3785
                                                                    =
                                                                    let uu____3788
                                                                    =
                                                                    mktac1
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3789
                                                                    =
                                                                    let uu____3792
                                                                    =
                                                                    mktac1
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3793
                                                                    =
                                                                    let uu____3796
                                                                    =
                                                                    mktac1
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3797
                                                                    =
                                                                    let uu____3800
                                                                    =
                                                                    mktac1
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3801
                                                                    =
                                                                    let uu____3804
                                                                    =
                                                                    mktac1
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3805
                                                                    =
                                                                    let uu____3808
                                                                    =
                                                                    let uu____3809
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac1
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____3809
                                                                     in
                                                                    let uu____3820
                                                                    =
                                                                    let uu____3823
                                                                    =
                                                                    mktac1
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____3824
                                                                    =
                                                                    let uu____3827
                                                                    =
                                                                    mktac1
                                                                    "cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____3828
                                                                    =
                                                                    let uu____3831
                                                                    =
                                                                    mktac1
                                                                    "cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3832
                                                                    =
                                                                    let uu____3835
                                                                    =
                                                                    mktac1
                                                                    "cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3836
                                                                    =
                                                                    let uu____3839
                                                                    =
                                                                    mktac1
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                     in
                                                                    let uu____3840
                                                                    =
                                                                    let uu____3843
                                                                    =
                                                                    mktac1
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3844
                                                                    =
                                                                    let uu____3847
                                                                    =
                                                                    mktac1
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____3848
                                                                    =
                                                                    let uu____3851
                                                                    =
                                                                    mktac1
                                                                    "ngoals"
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____3852
                                                                    =
                                                                    let uu____3855
                                                                    =
                                                                    mktac1
                                                                    "ngoals_smt"
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____3856
                                                                    =
                                                                    let uu____3859
                                                                    =
                                                                    mktac1
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____3860
                                                                    =
                                                                    let uu____3863
                                                                    =
                                                                    let uu____3864
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac2
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____3864
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3871
                                                                    =
                                                                    let uu____3874
                                                                    =
                                                                    mktac3
                                                                    "unify_env"
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____3875
                                                                    =
                                                                    let uu____3878
                                                                    =
                                                                    let uu____3879
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    mktac3
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____3879
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____3886
                                                                    =
                                                                    let uu____3889
                                                                    =
                                                                    mktac2
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                     in
                                                                    let uu____3890
                                                                    =
                                                                    let uu____3893
                                                                    =
                                                                    mktac1
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3894
                                                                    =
                                                                    let uu____3897
                                                                    =
                                                                    mktac1
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                     in
                                                                    let uu____3898
                                                                    =
                                                                    let uu____3901
                                                                    =
                                                                    mktac1
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    [uu____3901;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____3897
                                                                    ::
                                                                    uu____3898
                                                                     in
                                                                    uu____3893
                                                                    ::
                                                                    uu____3894
                                                                     in
                                                                    uu____3889
                                                                    ::
                                                                    uu____3890
                                                                     in
                                                                    uu____3878
                                                                    ::
                                                                    uu____3886
                                                                     in
                                                                    uu____3874
                                                                    ::
                                                                    uu____3875
                                                                     in
                                                                    uu____3863
                                                                    ::
                                                                    uu____3871
                                                                     in
                                                                    uu____3859
                                                                    ::
                                                                    uu____3860
                                                                     in
                                                                    uu____3855
                                                                    ::
                                                                    uu____3856
                                                                     in
                                                                    uu____3851
                                                                    ::
                                                                    uu____3852
                                                                     in
                                                                    uu____3847
                                                                    ::
                                                                    uu____3848
                                                                     in
                                                                    uu____3843
                                                                    ::
                                                                    uu____3844
                                                                     in
                                                                    uu____3839
                                                                    ::
                                                                    uu____3840
                                                                     in
                                                                    uu____3835
                                                                    ::
                                                                    uu____3836
                                                                     in
                                                                    uu____3831
                                                                    ::
                                                                    uu____3832
                                                                     in
                                                                    uu____3827
                                                                    ::
                                                                    uu____3828
                                                                     in
                                                                    uu____3823
                                                                    ::
                                                                    uu____3824
                                                                     in
                                                                    uu____3808
                                                                    ::
                                                                    uu____3820
                                                                     in
                                                                    uu____3804
                                                                    ::
                                                                    uu____3805
                                                                     in
                                                                    uu____3800
                                                                    ::
                                                                    uu____3801
                                                                     in
                                                                    uu____3796
                                                                    ::
                                                                    uu____3797
                                                                     in
                                                                    uu____3792
                                                                    ::
                                                                    uu____3793
                                                                     in
                                                                    uu____3788
                                                                    ::
                                                                    uu____3789
                                                                     in
                                                                    uu____3784
                                                                    ::
                                                                    uu____3785
                                                                     in
                                                                    uu____3780
                                                                    ::
                                                                    uu____3781
                                                                     in
                                                                    uu____3737
                                                                    ::
                                                                    uu____3777
                                                                     in
                                                                    uu____3726
                                                                    ::
                                                                    uu____3734
                                                                     in
                                                                    uu____3722
                                                                    ::
                                                                    uu____3723
                                                                     in
                                                                  uu____3718
                                                                    ::
                                                                    uu____3719
                                                                   in
                                                                uu____3714 ::
                                                                  uu____3715
                                                                 in
                                                              uu____3710 ::
                                                                uu____3711
                                                               in
                                                            uu____3706 ::
                                                              uu____3707
                                                             in
                                                          uu____3702 ::
                                                            uu____3703
                                                           in
                                                        uu____3698 ::
                                                          uu____3699
                                                         in
                                                      uu____3694 ::
                                                        uu____3695
                                                       in
                                                    uu____3690 :: uu____3691
                                                     in
                                                  uu____3686 :: uu____3687
                                                   in
                                                uu____3668 :: uu____3683  in
                                              uu____3635 :: uu____3665  in
                                            uu____3631 :: uu____3632  in
                                          uu____3627 :: uu____3628  in
                                        uu____3623 :: uu____3624  in
                                      uu____3619 :: uu____3620  in
                                    uu____3615 :: uu____3616  in
                                  uu____3611 :: uu____3612  in
                                uu____3607 :: uu____3608  in
                              uu____3603 :: uu____3604  in
                            uu____3599 :: uu____3600  in
                          uu____3595 :: uu____3596  in
                        uu____3591 :: uu____3592  in
                      uu____3587 :: uu____3588  in
                    uu____3576 :: uu____3584  in
                  uu____3565 :: uu____3573  in
                uu____3554 :: uu____3562  in
              uu____3539 :: uu____3551  in
            uu____3535 :: uu____3536  in
          uu____3515 :: uu____3532  in
        uu____3511 :: uu____3512  in
      uu____3505 :: uu____3508  in
    FStar_List.append uu____3502
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
               let uu____3924 =
                 let uu____3929 =
                   let uu____3930 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____3930]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____3929  in
               uu____3924 FStar_Pervasives_Native.None rng  in
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
             let uu____3977 =
               let uu____3982 =
                 let uu____3983 =
                   let uu____3992 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____3992  in
                 [uu____3983]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3982  in
             uu____3977 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           if proof_state.FStar_Tactics_Types.tac_verb_dbg
           then
             (let uu____4015 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____4015)
           else ();
           (let result =
              let uu____4018 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____4018 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            if proof_state.FStar_Tactics_Types.tac_verb_dbg
            then
              (let uu____4022 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____4022)
            else ();
            (let res =
               let uu____4029 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Syntax_Embeddings.unembed uu____4029 result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____4042 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____4042
                   (fun uu____4046  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____4051 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____4051
                   (fun uu____4055  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____4058 =
                   let uu____4063 =
                     let uu____4064 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____4064
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____4063)  in
                 FStar_Errors.raise_error uu____4058
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      let uu____4071 = unembed_tactic_0 eb embedded_tac_b  in
      FStar_All.pipe_left (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
        uu____4071

let unembed_tactic_1_alt :
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
               let uu____4140 =
                 let uu____4145 =
                   let uu____4146 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____4146]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____4145  in
               uu____4140 FStar_Pervasives_Native.None rng  in
             let app1 = FStar_Syntax_Util.mk_reify app  in
             unembed_tactic_0 er app1)
  
let e_tactic_1_alt :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a ->
           FStar_Tactics_Types.proofstate -> 'r FStar_Tactics_Result.__result)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let em rng u =
        let uu___340_4239 = FStar_Syntax_Util.exp_unit  in
        {
          FStar_Syntax_Syntax.n = (uu___340_4239.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___340_4239.FStar_Syntax_Syntax.vars)
        }  in
      let un w t0 =
        let uu____4271 = unembed_tactic_1_alt ea er t0  in
        match uu____4271 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____4311 = f x  in FStar_Tactics_Basic.run uu____4311))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let typ = FStar_Syntax_Syntax.t_term  in
      FStar_Syntax_Embeddings.mk_emb em un typ
  
let report_implicits :
  'Auu____4342 . 'Auu____4342 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____4371 =
               let uu____4372 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____4373 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____4372 uu____4373 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____4371, (imp.FStar_TypeChecker_Env.imp_range))) is
         in
      FStar_Errors.add_errors errs
  
let (run_tactic_on_typ :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.typ ->
            (FStar_Tactics_Basic.goal Prims.list,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2)
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun typ  ->
            (let uu____4412 = FStar_ST.op_Bang tacdbg  in
             if uu____4412
             then
               let uu____4432 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "About to reduce uvars on: (%s) {\n"
                 uu____4432
             else ());
            (let tactic1 =
               FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic
                in
             (let uu____4436 = FStar_ST.op_Bang tacdbg  in
              if uu____4436
              then
                let uu____4456 = FStar_Syntax_Print.term_to_string tactic1
                   in
                FStar_Util.print1 "}\nTypechecking tactic: (%s) {\n"
                  uu____4456
              else ());
             (let uu____4458 =
                FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
              match uu____4458 with
              | (uu____4471,uu____4472,g) ->
                  ((let uu____4475 = FStar_ST.op_Bang tacdbg  in
                    if uu____4475 then FStar_Util.print_string "}\n" else ());
                   FStar_TypeChecker_Rel.force_trivial_guard env g;
                   FStar_Errors.stop_if_err ();
                   (let tau =
                      unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic1
                       in
                    let uu____4501 =
                      FStar_TypeChecker_Env.clear_expected_typ env  in
                    match uu____4501 with
                    | (env1,uu____4515) ->
                        let env2 =
                          let uu___341_4521 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___341_4521.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___341_4521.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___341_4521.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___341_4521.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___341_4521.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___341_4521.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___341_4521.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___341_4521.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___341_4521.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___341_4521.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___341_4521.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp = false;
                            FStar_TypeChecker_Env.effects =
                              (uu___341_4521.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___341_4521.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___341_4521.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___341_4521.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___341_4521.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___341_4521.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___341_4521.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___341_4521.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___341_4521.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___341_4521.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___341_4521.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___341_4521.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___341_4521.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___341_4521.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___341_4521.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___341_4521.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___341_4521.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___341_4521.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___341_4521.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___341_4521.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___341_4521.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___341_4521.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___341_4521.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___341_4521.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___341_4521.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___341_4521.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___341_4521.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___341_4521.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___341_4521.FStar_TypeChecker_Env.dep_graph)
                          }  in
                        let env3 =
                          let uu___342_4523 = env2  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___342_4523.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___342_4523.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___342_4523.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___342_4523.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___342_4523.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___342_4523.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___342_4523.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___342_4523.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___342_4523.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___342_4523.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___342_4523.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___342_4523.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___342_4523.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___342_4523.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___342_4523.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___342_4523.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___342_4523.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___342_4523.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___342_4523.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___342_4523.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___342_4523.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes = true;
                            FStar_TypeChecker_Env.phase1 =
                              (uu___342_4523.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___342_4523.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___342_4523.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___342_4523.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___342_4523.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___342_4523.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___342_4523.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___342_4523.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___342_4523.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___342_4523.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___342_4523.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___342_4523.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___342_4523.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___342_4523.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___342_4523.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___342_4523.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___342_4523.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___342_4523.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___342_4523.FStar_TypeChecker_Env.dep_graph)
                          }  in
                        let env4 =
                          let uu___343_4525 = env3  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___343_4525.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___343_4525.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___343_4525.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___343_4525.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___343_4525.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___343_4525.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___343_4525.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___343_4525.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___343_4525.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___343_4525.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___343_4525.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___343_4525.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___343_4525.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___343_4525.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___343_4525.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___343_4525.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___343_4525.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___343_4525.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___343_4525.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___343_4525.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___343_4525.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___343_4525.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___343_4525.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard = true;
                            FStar_TypeChecker_Env.nosynth =
                              (uu___343_4525.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___343_4525.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___343_4525.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___343_4525.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___343_4525.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___343_4525.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___343_4525.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___343_4525.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___343_4525.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___343_4525.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___343_4525.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___343_4525.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___343_4525.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___343_4525.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___343_4525.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___343_4525.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___343_4525.FStar_TypeChecker_Env.dep_graph)
                          }  in
                        let rng =
                          let uu____4527 = FStar_Range.use_range rng_goal  in
                          let uu____4528 = FStar_Range.use_range rng_tac  in
                          FStar_Range.range_of_rng uu____4527 uu____4528  in
                        let uu____4529 =
                          FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                            typ
                           in
                        (match uu____4529 with
                         | (ps,w) ->
                             (FStar_ST.op_Colon_Equals
                                FStar_Reflection_Basic.env_hook
                                (FStar_Pervasives_Native.Some env4);
                              (let uu____4567 = FStar_ST.op_Bang tacdbg  in
                               if uu____4567
                               then
                                 let uu____4587 =
                                   FStar_Syntax_Print.term_to_string typ  in
                                 FStar_Util.print1
                                   "Running tactic with goal = (%s) {\n"
                                   uu____4587
                               else ());
                              (let uu____4589 =
                                 FStar_Util.record_time
                                   (fun uu____4599  ->
                                      FStar_Tactics_Basic.run_safe tau ps)
                                  in
                               match uu____4589 with
                               | (res,ms) ->
                                   ((let uu____4613 = FStar_ST.op_Bang tacdbg
                                        in
                                     if uu____4613
                                     then
                                       let uu____4633 =
                                         FStar_Syntax_Print.term_to_string
                                           tactic1
                                          in
                                       let uu____4634 =
                                         FStar_Util.string_of_int ms  in
                                       let uu____4635 =
                                         FStar_Syntax_Print.lid_to_string
                                           env4.FStar_TypeChecker_Env.curmodule
                                          in
                                       FStar_Util.print3
                                         "}\nTactic %s ran in %s ms (%s)\n"
                                         uu____4633 uu____4634 uu____4635
                                     else ());
                                    (match res with
                                     | FStar_Tactics_Result.Success
                                         (uu____4643,ps1) ->
                                         ((let uu____4646 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____4646
                                           then
                                             let uu____4666 =
                                               FStar_Syntax_Print.term_to_string
                                                 w
                                                in
                                             FStar_Util.print1
                                               "Tactic generated proofterm %s\n"
                                               uu____4666
                                           else ());
                                          FStar_List.iter
                                            (fun g1  ->
                                               let uu____4673 =
                                                 FStar_Tactics_Basic.is_irrelevant
                                                   g1
                                                  in
                                               if uu____4673
                                               then
                                                 let uu____4674 =
                                                   let uu____4675 =
                                                     FStar_Tactics_Types.goal_env
                                                       g1
                                                      in
                                                   let uu____4676 =
                                                     FStar_Tactics_Types.goal_witness
                                                       g1
                                                      in
                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                     uu____4675 uu____4676
                                                     FStar_Syntax_Util.exp_unit
                                                    in
                                                 (if uu____4674
                                                  then ()
                                                  else
                                                    (let uu____4678 =
                                                       let uu____4679 =
                                                         let uu____4680 =
                                                           FStar_Tactics_Types.goal_witness
                                                             g1
                                                            in
                                                         FStar_Syntax_Print.term_to_string
                                                           uu____4680
                                                          in
                                                       FStar_Util.format1
                                                         "Irrelevant tactic witness does not unify with (): %s"
                                                         uu____4679
                                                        in
                                                     failwith uu____4678))
                                               else ())
                                            (FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals);
                                          (let uu____4683 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____4683
                                           then
                                             let uu____4703 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print1
                                               "About to check tactic implicits: %s\n"
                                               uu____4703
                                           else ());
                                          (let g1 =
                                             let uu___344_4708 =
                                               FStar_TypeChecker_Env.trivial_guard
                                                in
                                             {
                                               FStar_TypeChecker_Env.guard_f
                                                 =
                                                 (uu___344_4708.FStar_TypeChecker_Env.guard_f);
                                               FStar_TypeChecker_Env.deferred
                                                 =
                                                 (uu___344_4708.FStar_TypeChecker_Env.deferred);
                                               FStar_TypeChecker_Env.univ_ineqs
                                                 =
                                                 (uu___344_4708.FStar_TypeChecker_Env.univ_ineqs);
                                               FStar_TypeChecker_Env.implicits
                                                 =
                                                 (ps1.FStar_Tactics_Types.all_implicits)
                                             }  in
                                           let g2 =
                                             FStar_TypeChecker_Rel.solve_deferred_constraints
                                               env4 g1
                                              in
                                           (let uu____4711 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____4711
                                            then
                                              let uu____4731 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print1
                                                "Checked (1) implicits: %s\n"
                                                uu____4731
                                            else ());
                                           (let g3 =
                                              FStar_TypeChecker_Rel.resolve_implicits_tac
                                                env4 g2
                                               in
                                            (let uu____4737 =
                                               FStar_ST.op_Bang tacdbg  in
                                             if uu____4737
                                             then
                                               let uu____4757 =
                                                 FStar_Common.string_of_list
                                                   (fun imp  ->
                                                      FStar_Syntax_Print.ctx_uvar_to_string
                                                        imp.FStar_TypeChecker_Env.imp_uvar)
                                                   ps1.FStar_Tactics_Types.all_implicits
                                                  in
                                               FStar_Util.print1
                                                 "Checked (2) implicits: %s\n"
                                                 uu____4757
                                             else ());
                                            report_implicits ps1
                                              g3.FStar_TypeChecker_Env.implicits;
                                            ((FStar_List.append
                                                ps1.FStar_Tactics_Types.goals
                                                ps1.FStar_Tactics_Types.smt_goals),
                                              w))))
                                     | FStar_Tactics_Result.Failed (s,ps1) ->
                                         ((let uu____4767 =
                                             let uu____4768 =
                                               FStar_TypeChecker_Normalize.psc_subst
                                                 ps1.FStar_Tactics_Types.psc
                                                in
                                             FStar_Tactics_Types.subst_proof_state
                                               uu____4768 ps1
                                              in
                                           FStar_Tactics_Basic.dump_proofstate
                                             uu____4767
                                             "at the time of failure");
                                          (let uu____4769 =
                                             let uu____4774 =
                                               FStar_Util.format1
                                                 "user tactic failed: %s" s
                                                in
                                             (FStar_Errors.Fatal_UserTacticFailure,
                                               uu____4774)
                                              in
                                           FStar_Errors.raise_error
                                             uu____4769
                                             ps1.FStar_Tactics_Types.entry_range)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____4786 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____4792 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____4798 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____4853 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____4893 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____4947 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____4988 . 'Auu____4988 -> 'Auu____4988 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____5016 = FStar_Syntax_Util.head_and_args t  in
        match uu____5016 with
        | (hd1,args) ->
            let uu____5059 =
              let uu____5074 =
                let uu____5075 = FStar_Syntax_Util.un_uinst hd1  in
                uu____5075.FStar_Syntax_Syntax.n  in
              (uu____5074, args)  in
            (match uu____5059 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____5090))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____5153 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____5153 with
                       | (gs,uu____5161) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____5168 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____5168 with
                       | (gs,uu____5176) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____5219 =
                        let uu____5226 =
                          let uu____5229 =
                            let uu____5230 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____5230
                             in
                          [uu____5229]  in
                        (FStar_Syntax_Util.t_true, uu____5226)  in
                      Simplified uu____5219
                  | Both  ->
                      let uu____5241 =
                        let uu____5250 =
                          let uu____5253 =
                            let uu____5254 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____5254
                             in
                          [uu____5253]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____5250)  in
                      Dual uu____5241
                  | Neg  -> Simplified (assertion, []))
             | uu____5267 -> Unchanged t)
  
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
    fun uu___339_5357  ->
      match uu___339_5357 with
      | Unchanged t -> let uu____5363 = f t  in Unchanged uu____5363
      | Simplified (t,gs) ->
          let uu____5370 = let uu____5377 = f t  in (uu____5377, gs)  in
          Simplified uu____5370
      | Dual (tn,tp,gs) ->
          let uu____5387 =
            let uu____5396 = f tn  in
            let uu____5397 = f tp  in (uu____5396, uu____5397, gs)  in
          Dual uu____5387
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____5460 = f t1 t2  in Unchanged uu____5460
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____5472 = let uu____5479 = f t1 t2  in (uu____5479, gs)
               in
            Simplified uu____5472
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____5493 = let uu____5500 = f t1 t2  in (uu____5500, gs)
               in
            Simplified uu____5493
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____5519 =
              let uu____5526 = f t1 t2  in
              (uu____5526, (FStar_List.append gs1 gs2))  in
            Simplified uu____5519
        | uu____5529 ->
            let uu____5538 = explode x  in
            (match uu____5538 with
             | (n1,p1,gs1) ->
                 let uu____5556 = explode y  in
                 (match uu____5556 with
                  | (n2,p2,gs2) ->
                      let uu____5574 =
                        let uu____5583 = f n1 n2  in
                        let uu____5584 = f p1 p2  in
                        (uu____5583, uu____5584, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____5574))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____5656 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____5656
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____5704  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____5746 =
              let uu____5747 = FStar_Syntax_Subst.compress t  in
              uu____5747.FStar_Syntax_Syntax.n  in
            match uu____5746 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____5759 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____5759 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____5785 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____5785 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____5805;
                   FStar_Syntax_Syntax.vars = uu____5806;_},(p,uu____5808)::
                 (q,uu____5810)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____5866 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5866
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____5869 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____5869 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____5883 = FStar_Syntax_Util.mk_imp l r  in
                       uu____5883.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____5887;
                   FStar_Syntax_Syntax.vars = uu____5888;_},(p,uu____5890)::
                 (q,uu____5892)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____5948 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5948
                   in
                let xq =
                  let uu____5950 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5950
                   in
                let r1 =
                  let uu____5952 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____5952 p  in
                let r2 =
                  let uu____5954 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____5954 q  in
                (match (r1, r2) with
                 | (Unchanged uu____5961,Unchanged uu____5962) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____5980 = FStar_Syntax_Util.mk_iff l r  in
                            uu____5980.FStar_Syntax_Syntax.n) r1 r2
                 | uu____5983 ->
                     let uu____5992 = explode r1  in
                     (match uu____5992 with
                      | (pn,pp,gs1) ->
                          let uu____6010 = explode r2  in
                          (match uu____6010 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____6031 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____6034 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____6031
                                   uu____6034
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____6098  ->
                       fun r  ->
                         match uu____6098 with
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
                let uu____6250 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____6250 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____6290  ->
                            match uu____6290 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____6312 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___345_6344 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___345_6344.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___345_6344.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____6312 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____6372 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____6372.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____6418 = traverse f pol e t1  in
                let uu____6423 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____6423 uu____6418
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___346_6463 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___346_6463.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___346_6463.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____6470 =
                f pol e
                  (let uu___347_6474 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___347_6474.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___347_6474.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____6470
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___348_6484 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___348_6484.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___348_6484.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____6485 = explode rp  in
              (match uu____6485 with
               | (uu____6494,p',gs') ->
                   Dual
                     ((let uu___349_6504 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___349_6504.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___349_6504.FStar_Syntax_Syntax.vars)
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
            FStar_Syntax_Syntax.delta_constant] e t
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
      (let uu____6547 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____6547);
      (let uu____6568 = FStar_ST.op_Bang tacdbg  in
       if uu____6568
       then
         let uu____6588 =
           let uu____6589 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____6589
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____6590 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____6588
           uu____6590
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____6619 =
         let uu____6628 = traverse by_tactic_interp Pos env goal  in
         match uu____6628 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____6652 -> failwith "no"  in
       match uu____6619 with
       | (t',gs) ->
           ((let uu____6680 = FStar_ST.op_Bang tacdbg  in
             if uu____6680
             then
               let uu____6700 =
                 let uu____6701 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____6701
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____6702 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____6700 uu____6702
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____6750  ->
                    fun g  ->
                      match uu____6750 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____6795 =
                              let uu____6798 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____6799 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____6798 uu____6799  in
                            match uu____6795 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____6800 =
                                  let uu____6805 =
                                    let uu____6806 =
                                      let uu____6807 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____6807
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____6806
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____6805)
                                   in
                                FStar_Errors.raise_error uu____6800
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____6810 = FStar_ST.op_Bang tacdbg  in
                            if uu____6810
                            then
                              let uu____6830 = FStar_Util.string_of_int n1
                                 in
                              let uu____6831 =
                                let uu____6832 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____6832
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____6830 uu____6831
                            else ());
                           (let gt' =
                              let uu____6835 =
                                let uu____6836 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____6836
                                 in
                              FStar_TypeChecker_Util.label uu____6835
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____6837 =
                              let uu____6846 =
                                let uu____6853 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____6853, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____6846 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____6837)))) s
                 gs
                in
             let uu____6868 = s1  in
             match uu____6868 with
             | (uu____6889,gs1) ->
                 let uu____6907 =
                   let uu____6914 = FStar_Options.peek ()  in
                   (env, t', uu____6914)  in
                 uu____6907 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____6927 =
        let uu____6928 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____6928  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____6927 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____6929 =
      let uu____6934 =
        let uu____6935 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____6944 =
          let uu____6955 = FStar_Syntax_Syntax.as_arg a  in [uu____6955]  in
        uu____6935 :: uu____6944  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____6934  in
    uu____6929 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        if env.FStar_TypeChecker_Env.nosynth
        then
          let uu____7005 =
            let uu____7010 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____7011 =
              let uu____7012 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____7012]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____7010 uu____7011  in
          uu____7005 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____7041 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____7041);
           (let uu____7061 =
              let uu____7068 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____7068 env typ
               in
            match uu____7061 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____7082 =
                        let uu____7085 = FStar_Tactics_Types.goal_env g  in
                        let uu____7086 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____7085 uu____7086  in
                      match uu____7082 with
                      | FStar_Pervasives_Native.Some vc ->
                          let guard =
                            {
                              FStar_TypeChecker_Env.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Env.deferred = [];
                              FStar_TypeChecker_Env.univ_ineqs = ([], []);
                              FStar_TypeChecker_Env.implicits = []
                            }  in
                          let uu____7097 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____7097 guard
                      | FStar_Pervasives_Native.None  ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                              "synthesis left open goals")
                            typ.FStar_Syntax_Syntax.pos) gs;
                 w)))
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      if env.FStar_TypeChecker_Env.nosynth
      then []
      else
        ((let uu____7114 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____7114);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____7135 =
            let uu____7142 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____7142 env typ
             in
          match uu____7135 with
          | (gs,w) ->
              ((let uu____7152 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____7156 =
                         let uu____7157 =
                           let uu____7160 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____7161 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____7160 uu____7161  in
                         FStar_Option.isSome uu____7157  in
                       Prims.op_Negation uu____7156) gs
                   in
                if uu____7152
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
                      FStar_Syntax_Syntax.delta_constant;
                    FStar_TypeChecker_Normalize.Primops;
                    FStar_TypeChecker_Normalize.Unascribe;
                    FStar_TypeChecker_Normalize.Unmeta] env w
                   in
                (let uu____7165 = FStar_ST.op_Bang tacdbg  in
                 if uu____7165
                 then
                   let uu____7185 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____7185
                 else ());
                (let uu____7187 =
                   let uu____7192 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Syntax_Embeddings.unembed uu____7192 w1  in
                 match uu____7187 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  