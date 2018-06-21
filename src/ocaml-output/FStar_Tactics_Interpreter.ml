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
      (fun uu____2051  ->
         fun uu____2052  -> failwith "Impossible: embedding tactic (0)?")
      (fun w  ->
         fun t  ->
           let uu____2060 = unembed_tactic_0 er t  in
           FStar_All.pipe_left
             (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____2060)
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
        (fun uu____2084  ->
           fun uu____2085  -> failwith "Impossible: embedding tactic (1)?")
        (fun w  -> fun t  -> unembed_tactic_1 ea er t)
        FStar_Syntax_Syntax.t_unit

and (primitive_steps :
  unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____2094  ->
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
      | (ps,uu____2500)::[] ->
          let uu____2525 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2525
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2533 =
                 let uu____2534 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2535 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2534 uu____2535
                  in
               FStar_Pervasives_Native.Some uu____2533)
      | uu____2536 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____2540 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2540;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____2557)::[] ->
          let uu____2582 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2582
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2590 =
                 let uu____2591 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2592 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2591 uu____2592
                  in
               FStar_Pervasives_Native.Some uu____2590)
      | uu____2593 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____2597 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2597;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____2614)::[] ->
          let uu____2639 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2639
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2648 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2667)::(r,uu____2669)::[] ->
          let uu____2710 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2710
            (fun ps1  ->
               let uu____2716 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_range r
                  in
               FStar_Util.bind_opt uu____2716
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2724 =
                      let uu____2725 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Syntax_Embeddings.embed
                        FStar_Tactics_Embedding.e_proofstate uu____2725 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2724))
      | uu____2726 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____2745)::(b,uu____2747)::[] ->
          let uu____2788 =
            FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_env
              env_t
             in
          FStar_Util.bind_opt uu____2788
            (fun env  ->
               let uu____2794 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Reflection_Embeddings.e_binder b
                  in
               FStar_Util.bind_opt uu____2794
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____2814 =
                      FStar_Syntax_Embeddings.embed
                        FStar_Reflection_Embeddings.e_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____2814))
      | uu____2815 -> failwith "Unexpected application of push_binder"  in
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
    let uu____2824 =
      let uu____2827 =
        mktac2 "fail" (fun uu____2829  -> FStar_Tactics_Basic.fail)
          FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string
          FStar_Syntax_Embeddings.e_any
         in
      let uu____2830 =
        let uu____2833 =
          mktac1 "trivial" FStar_Tactics_Basic.trivial
            FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
           in
        let uu____2834 =
          let uu____2837 =
            let uu____2838 = e_tactic_0' FStar_Syntax_Embeddings.e_any  in
            let uu____2843 =
              FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any
               in
            mktac2 "__trytac" (fun uu____2853  -> FStar_Tactics_Basic.trytac)
              FStar_Syntax_Embeddings.e_any uu____2838 uu____2843
             in
          let uu____2854 =
            let uu____2857 =
              mktac1 "intro" FStar_Tactics_Basic.intro
                FStar_Syntax_Embeddings.e_unit
                FStar_Reflection_Embeddings.e_binder
               in
            let uu____2858 =
              let uu____2861 =
                let uu____2862 =
                  FStar_Syntax_Embeddings.e_tuple2
                    FStar_Reflection_Embeddings.e_binder
                    FStar_Reflection_Embeddings.e_binder
                   in
                mktac1 "intro_rec" FStar_Tactics_Basic.intro_rec
                  FStar_Syntax_Embeddings.e_unit uu____2862
                 in
              let uu____2873 =
                let uu____2876 =
                  let uu____2877 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Syntax_Embeddings.e_norm_step
                     in
                  mktac1 "norm" FStar_Tactics_Basic.norm uu____2877
                    FStar_Syntax_Embeddings.e_unit
                   in
                let uu____2884 =
                  let uu____2887 =
                    let uu____2888 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_norm_step
                       in
                    mktac3 "norm_term_env" FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Embeddings.e_env uu____2888
                      FStar_Reflection_Embeddings.e_term
                      FStar_Reflection_Embeddings.e_term
                     in
                  let uu____2895 =
                    let uu____2898 =
                      let uu____2899 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step
                         in
                      mktac2 "norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____2899
                        FStar_Reflection_Embeddings.e_binder
                        FStar_Syntax_Embeddings.e_unit
                       in
                    let uu____2906 =
                      let uu____2909 =
                        mktac2 "rename_to" FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_string
                          FStar_Syntax_Embeddings.e_unit
                         in
                      let uu____2910 =
                        let uu____2913 =
                          mktac1 "binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_unit
                           in
                        let uu____2914 =
                          let uu____2917 =
                            mktac1 "revert" FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Syntax_Embeddings.e_unit
                             in
                          let uu____2918 =
                            let uu____2921 =
                              mktac1 "clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit
                               in
                            let uu____2922 =
                              let uu____2925 =
                                mktac1 "clear" FStar_Tactics_Basic.clear
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                 in
                              let uu____2926 =
                                let uu____2929 =
                                  mktac1 "rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_unit
                                   in
                                let uu____2930 =
                                  let uu____2933 =
                                    mktac1 "smt" FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                     in
                                  let uu____2934 =
                                    let uu____2937 =
                                      mktac1 "refine_intro"
                                        FStar_Tactics_Basic.refine_intro
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                       in
                                    let uu____2938 =
                                      let uu____2941 =
                                        mktac2 "t_exact"
                                          FStar_Tactics_Basic.t_exact
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Syntax_Embeddings.e_unit
                                         in
                                      let uu____2942 =
                                        let uu____2945 =
                                          mktac1 "apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_unit
                                           in
                                        let uu____2946 =
                                          let uu____2949 =
                                            mktac1 "apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Embeddings.e_term
                                              FStar_Syntax_Embeddings.e_unit
                                             in
                                          let uu____2950 =
                                            let uu____2953 =
                                              mktac1 "apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Syntax_Embeddings.e_unit
                                               in
                                            let uu____2954 =
                                              let uu____2957 =
                                                let uu____2958 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____2963 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____2968 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Syntax_Embeddings.e_any
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                mktac5 "__divide"
                                                  (fun uu____2985  ->
                                                     fun uu____2986  ->
                                                       FStar_Tactics_Basic.divide)
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_int
                                                  uu____2958 uu____2963
                                                  uu____2968
                                                 in
                                              let uu____2987 =
                                                let uu____2990 =
                                                  let uu____2991 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____2996 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  mktac2 "__seq"
                                                    FStar_Tactics_Basic.seq
                                                    uu____2991 uu____2996
                                                    FStar_Syntax_Embeddings.e_unit
                                                   in
                                                let uu____3005 =
                                                  let uu____3008 =
                                                    mktac1 "set_options"
                                                      FStar_Tactics_Basic.set_options
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____3009 =
                                                    let uu____3012 =
                                                      mktac1 "tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Reflection_Embeddings.e_term
                                                       in
                                                    let uu____3013 =
                                                      let uu____3016 =
                                                        mktac1 "unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_unit
                                                         in
                                                      let uu____3017 =
                                                        let uu____3020 =
                                                          mktac2 "unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Reflection_Embeddings.e_term
                                                            FStar_Syntax_Embeddings.e_any
                                                           in
                                                        let uu____3021 =
                                                          let uu____3024 =
                                                            mktac1 "prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.e_string
                                                              FStar_Syntax_Embeddings.e_unit
                                                             in
                                                          let uu____3025 =
                                                            let uu____3028 =
                                                              mktac1 "addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____3029 =
                                                              let uu____3032
                                                                =
                                                                mktac1
                                                                  "print"
                                                                  FStar_Tactics_Basic.print
                                                                  FStar_Syntax_Embeddings.e_string
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                 in
                                                              let uu____3033
                                                                =
                                                                let uu____3036
                                                                  =
                                                                  mktac1
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                   in
                                                                let uu____3037
                                                                  =
                                                                  let uu____3040
                                                                    =
                                                                    mktac1
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                  let uu____3041
                                                                    =
                                                                    let uu____3044
                                                                    =
                                                                    mktac1
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3045
                                                                    =
                                                                    let uu____3048
                                                                    =
                                                                    let uu____3049
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____3049
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3056
                                                                    =
                                                                    let uu____3059
                                                                    =
                                                                    let uu____3060
                                                                    =
                                                                    let uu____3072
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____3072
                                                                     in
                                                                    let uu____3083
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____3060
                                                                    uu____3083
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3099
                                                                    =
                                                                    let uu____3102
                                                                    =
                                                                    mktac1
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3103
                                                                    =
                                                                    let uu____3106
                                                                    =
                                                                    mktac1
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3107
                                                                    =
                                                                    let uu____3110
                                                                    =
                                                                    mktac1
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3111
                                                                    =
                                                                    let uu____3114
                                                                    =
                                                                    mktac1
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3115
                                                                    =
                                                                    let uu____3118
                                                                    =
                                                                    mktac1
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3119
                                                                    =
                                                                    let uu____3122
                                                                    =
                                                                    mktac1
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3123
                                                                    =
                                                                    let uu____3126
                                                                    =
                                                                    mktac1
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3127
                                                                    =
                                                                    let uu____3130
                                                                    =
                                                                    let uu____3131
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac1
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____3131
                                                                     in
                                                                    let uu____3142
                                                                    =
                                                                    let uu____3145
                                                                    =
                                                                    mktac1
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____3146
                                                                    =
                                                                    let uu____3149
                                                                    =
                                                                    mktac1
                                                                    "cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____3150
                                                                    =
                                                                    let uu____3153
                                                                    =
                                                                    mktac1
                                                                    "cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3154
                                                                    =
                                                                    let uu____3157
                                                                    =
                                                                    mktac1
                                                                    "cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3158
                                                                    =
                                                                    let uu____3161
                                                                    =
                                                                    mktac1
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                     in
                                                                    let uu____3162
                                                                    =
                                                                    let uu____3165
                                                                    =
                                                                    mktac1
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3166
                                                                    =
                                                                    let uu____3169
                                                                    =
                                                                    mktac1
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____3170
                                                                    =
                                                                    let uu____3173
                                                                    =
                                                                    mktac1
                                                                    "ngoals"
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____3174
                                                                    =
                                                                    let uu____3177
                                                                    =
                                                                    mktac1
                                                                    "ngoals_smt"
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____3178
                                                                    =
                                                                    let uu____3181
                                                                    =
                                                                    mktac1
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____3182
                                                                    =
                                                                    let uu____3185
                                                                    =
                                                                    let uu____3186
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac2
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____3186
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3193
                                                                    =
                                                                    let uu____3196
                                                                    =
                                                                    mktac3
                                                                    "unify_env"
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____3197
                                                                    =
                                                                    let uu____3200
                                                                    =
                                                                    let uu____3201
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    mktac3
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____3201
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____3208
                                                                    =
                                                                    let uu____3211
                                                                    =
                                                                    mktac2
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                     in
                                                                    let uu____3212
                                                                    =
                                                                    let uu____3215
                                                                    =
                                                                    mktac1
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3216
                                                                    =
                                                                    let uu____3219
                                                                    =
                                                                    mktac1
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                     in
                                                                    let uu____3220
                                                                    =
                                                                    let uu____3223
                                                                    =
                                                                    mktac1
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    [uu____3223;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____3219
                                                                    ::
                                                                    uu____3220
                                                                     in
                                                                    uu____3215
                                                                    ::
                                                                    uu____3216
                                                                     in
                                                                    uu____3211
                                                                    ::
                                                                    uu____3212
                                                                     in
                                                                    uu____3200
                                                                    ::
                                                                    uu____3208
                                                                     in
                                                                    uu____3196
                                                                    ::
                                                                    uu____3197
                                                                     in
                                                                    uu____3185
                                                                    ::
                                                                    uu____3193
                                                                     in
                                                                    uu____3181
                                                                    ::
                                                                    uu____3182
                                                                     in
                                                                    uu____3177
                                                                    ::
                                                                    uu____3178
                                                                     in
                                                                    uu____3173
                                                                    ::
                                                                    uu____3174
                                                                     in
                                                                    uu____3169
                                                                    ::
                                                                    uu____3170
                                                                     in
                                                                    uu____3165
                                                                    ::
                                                                    uu____3166
                                                                     in
                                                                    uu____3161
                                                                    ::
                                                                    uu____3162
                                                                     in
                                                                    uu____3157
                                                                    ::
                                                                    uu____3158
                                                                     in
                                                                    uu____3153
                                                                    ::
                                                                    uu____3154
                                                                     in
                                                                    uu____3149
                                                                    ::
                                                                    uu____3150
                                                                     in
                                                                    uu____3145
                                                                    ::
                                                                    uu____3146
                                                                     in
                                                                    uu____3130
                                                                    ::
                                                                    uu____3142
                                                                     in
                                                                    uu____3126
                                                                    ::
                                                                    uu____3127
                                                                     in
                                                                    uu____3122
                                                                    ::
                                                                    uu____3123
                                                                     in
                                                                    uu____3118
                                                                    ::
                                                                    uu____3119
                                                                     in
                                                                    uu____3114
                                                                    ::
                                                                    uu____3115
                                                                     in
                                                                    uu____3110
                                                                    ::
                                                                    uu____3111
                                                                     in
                                                                    uu____3106
                                                                    ::
                                                                    uu____3107
                                                                     in
                                                                    uu____3102
                                                                    ::
                                                                    uu____3103
                                                                     in
                                                                    uu____3059
                                                                    ::
                                                                    uu____3099
                                                                     in
                                                                    uu____3048
                                                                    ::
                                                                    uu____3056
                                                                     in
                                                                    uu____3044
                                                                    ::
                                                                    uu____3045
                                                                     in
                                                                  uu____3040
                                                                    ::
                                                                    uu____3041
                                                                   in
                                                                uu____3036 ::
                                                                  uu____3037
                                                                 in
                                                              uu____3032 ::
                                                                uu____3033
                                                               in
                                                            uu____3028 ::
                                                              uu____3029
                                                             in
                                                          uu____3024 ::
                                                            uu____3025
                                                           in
                                                        uu____3020 ::
                                                          uu____3021
                                                         in
                                                      uu____3016 ::
                                                        uu____3017
                                                       in
                                                    uu____3012 :: uu____3013
                                                     in
                                                  uu____3008 :: uu____3009
                                                   in
                                                uu____2990 :: uu____3005  in
                                              uu____2957 :: uu____2987  in
                                            uu____2953 :: uu____2954  in
                                          uu____2949 :: uu____2950  in
                                        uu____2945 :: uu____2946  in
                                      uu____2941 :: uu____2942  in
                                    uu____2937 :: uu____2938  in
                                  uu____2933 :: uu____2934  in
                                uu____2929 :: uu____2930  in
                              uu____2925 :: uu____2926  in
                            uu____2921 :: uu____2922  in
                          uu____2917 :: uu____2918  in
                        uu____2913 :: uu____2914  in
                      uu____2909 :: uu____2910  in
                    uu____2898 :: uu____2906  in
                  uu____2887 :: uu____2895  in
                uu____2876 :: uu____2884  in
              uu____2861 :: uu____2873  in
            uu____2857 :: uu____2858  in
          uu____2837 :: uu____2854  in
        uu____2833 :: uu____2834  in
      uu____2827 :: uu____2830  in
    FStar_List.append uu____2824
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
               let uu____3246 =
                 let uu____3251 =
                   let uu____3252 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____3252]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____3251  in
               uu____3246 FStar_Pervasives_Native.None rng  in
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
             let uu____3299 =
               let uu____3304 =
                 let uu____3305 =
                   let uu____3314 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____3314  in
                 [uu____3305]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3304  in
             uu____3299 FStar_Pervasives_Native.None rng  in
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
             (let uu____3337 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____3337)
           else ();
           (let result =
              let uu____3340 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____3340 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            if proof_state.FStar_Tactics_Types.tac_verb_dbg
            then
              (let uu____3344 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____3344)
            else ();
            (let res =
               let uu____3351 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Syntax_Embeddings.unembed uu____3351 result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____3364 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3364
                   (fun uu____3368  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____3373 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____3373
                   (fun uu____3377  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____3380 =
                   let uu____3385 =
                     let uu____3386 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____3386
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____3385)  in
                 FStar_Errors.raise_error uu____3380
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      let uu____3393 = unembed_tactic_0 eb embedded_tac_b  in
      FStar_All.pipe_left (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
        uu____3393

let report_implicits :
  'Auu____3410 . 'Auu____3410 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____3439 =
               let uu____3440 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____3441 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____3440 uu____3441 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____3439, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____3480 = FStar_ST.op_Bang tacdbg  in
             if uu____3480
             then
               let uu____3504 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "About to reduce uvars on: %s\n" uu____3504
             else ());
            (let tactic1 =
               FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic
                in
             (let uu____3508 = FStar_ST.op_Bang tacdbg  in
              if uu____3508
              then
                let uu____3532 = FStar_Syntax_Print.term_to_string tactic1
                   in
                FStar_Util.print1 "About to check tactic term: %s\n"
                  uu____3532
              else ());
             (let uu____3534 =
                FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
              match uu____3534 with
              | (uu____3547,uu____3548,g) ->
                  (FStar_TypeChecker_Rel.force_trivial_guard env g;
                   FStar_Errors.stop_if_err ();
                   (let tau =
                      unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic1
                       in
                    let uu____3555 =
                      FStar_TypeChecker_Env.clear_expected_typ env  in
                    match uu____3555 with
                    | (env1,uu____3569) ->
                        let env2 =
                          let uu___339_3575 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___339_3575.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___339_3575.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___339_3575.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___339_3575.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___339_3575.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___339_3575.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___339_3575.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___339_3575.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___339_3575.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___339_3575.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___339_3575.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp = false;
                            FStar_TypeChecker_Env.effects =
                              (uu___339_3575.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___339_3575.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___339_3575.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___339_3575.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___339_3575.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___339_3575.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___339_3575.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___339_3575.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___339_3575.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___339_3575.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___339_3575.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___339_3575.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___339_3575.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___339_3575.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___339_3575.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___339_3575.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___339_3575.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___339_3575.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___339_3575.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___339_3575.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___339_3575.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___339_3575.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___339_3575.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___339_3575.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___339_3575.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___339_3575.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___339_3575.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___339_3575.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___339_3575.FStar_TypeChecker_Env.dep_graph)
                          }  in
                        let env3 =
                          let uu___340_3577 = env2  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___340_3577.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___340_3577.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___340_3577.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___340_3577.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___340_3577.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___340_3577.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___340_3577.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___340_3577.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___340_3577.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___340_3577.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___340_3577.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___340_3577.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___340_3577.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___340_3577.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___340_3577.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___340_3577.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___340_3577.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___340_3577.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___340_3577.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___340_3577.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___340_3577.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes = true;
                            FStar_TypeChecker_Env.phase1 =
                              (uu___340_3577.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___340_3577.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___340_3577.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___340_3577.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___340_3577.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___340_3577.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___340_3577.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___340_3577.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___340_3577.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___340_3577.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___340_3577.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___340_3577.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___340_3577.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___340_3577.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___340_3577.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___340_3577.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___340_3577.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___340_3577.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___340_3577.FStar_TypeChecker_Env.dep_graph)
                          }  in
                        let rng =
                          let uu____3579 = FStar_Range.use_range rng_goal  in
                          let uu____3580 = FStar_Range.use_range rng_tac  in
                          FStar_Range.range_of_rng uu____3579 uu____3580  in
                        let uu____3581 =
                          FStar_Tactics_Basic.proofstate_of_goal_ty rng env3
                            typ
                           in
                        (match uu____3581 with
                         | (ps,w) ->
                             ((let uu____3595 = FStar_ST.op_Bang tacdbg  in
                               if uu____3595
                               then
                                 let uu____3619 =
                                   FStar_Syntax_Print.term_to_string typ  in
                                 FStar_Util.print1
                                   "Running tactic with goal = %s\n"
                                   uu____3619
                               else ());
                              (let uu____3621 =
                                 FStar_Util.record_time
                                   (fun uu____3631  ->
                                      FStar_Tactics_Basic.run tau ps)
                                  in
                               match uu____3621 with
                               | (res,ms) ->
                                   ((let uu____3645 = FStar_ST.op_Bang tacdbg
                                        in
                                     if uu____3645
                                     then
                                       let uu____3669 =
                                         FStar_Syntax_Print.term_to_string
                                           tactic1
                                          in
                                       let uu____3670 =
                                         FStar_Util.string_of_int ms  in
                                       let uu____3671 =
                                         FStar_Syntax_Print.lid_to_string
                                           env3.FStar_TypeChecker_Env.curmodule
                                          in
                                       FStar_Util.print3
                                         "Tactic %s ran in %s ms (%s)\n"
                                         uu____3669 uu____3670 uu____3671
                                     else ());
                                    (match res with
                                     | FStar_Tactics_Result.Success
                                         (uu____3679,ps1) ->
                                         ((let uu____3682 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____3682
                                           then
                                             let uu____3706 =
                                               FStar_Syntax_Print.term_to_string
                                                 w
                                                in
                                             FStar_Util.print1
                                               "Tactic generated proofterm %s\n"
                                               uu____3706
                                           else ());
                                          FStar_List.iter
                                            (fun g1  ->
                                               let uu____3713 =
                                                 FStar_Tactics_Basic.is_irrelevant
                                                   g1
                                                  in
                                               if uu____3713
                                               then
                                                 let uu____3714 =
                                                   let uu____3715 =
                                                     FStar_Tactics_Types.goal_env
                                                       g1
                                                      in
                                                   let uu____3716 =
                                                     FStar_Tactics_Types.goal_witness
                                                       g1
                                                      in
                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                     uu____3715 uu____3716
                                                     FStar_Syntax_Util.exp_unit
                                                    in
                                                 (if uu____3714
                                                  then ()
                                                  else
                                                    (let uu____3718 =
                                                       let uu____3719 =
                                                         let uu____3720 =
                                                           FStar_Tactics_Types.goal_witness
                                                             g1
                                                            in
                                                         FStar_Syntax_Print.term_to_string
                                                           uu____3720
                                                          in
                                                       FStar_Util.format1
                                                         "Irrelevant tactic witness does not unify with (): %s"
                                                         uu____3719
                                                        in
                                                     failwith uu____3718))
                                               else ())
                                            (FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals);
                                          (let uu____3723 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____3723
                                           then
                                             let uu____3747 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print1
                                               "About to check tactic implicits: %s\n"
                                               uu____3747
                                           else ());
                                          (let g1 =
                                             let uu___341_3752 =
                                               FStar_TypeChecker_Env.trivial_guard
                                                in
                                             {
                                               FStar_TypeChecker_Env.guard_f
                                                 =
                                                 (uu___341_3752.FStar_TypeChecker_Env.guard_f);
                                               FStar_TypeChecker_Env.deferred
                                                 =
                                                 (uu___341_3752.FStar_TypeChecker_Env.deferred);
                                               FStar_TypeChecker_Env.univ_ineqs
                                                 =
                                                 (uu___341_3752.FStar_TypeChecker_Env.univ_ineqs);
                                               FStar_TypeChecker_Env.implicits
                                                 =
                                                 (ps1.FStar_Tactics_Types.all_implicits)
                                             }  in
                                           let g2 =
                                             FStar_TypeChecker_Rel.solve_deferred_constraints
                                               env3 g1
                                              in
                                           (let uu____3755 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____3755
                                            then
                                              let uu____3779 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print1
                                                "Checked (1) implicits: %s\n"
                                                uu____3779
                                            else ());
                                           (let g3 =
                                              FStar_TypeChecker_Rel.resolve_implicits_tac
                                                env3 g2
                                               in
                                            (let uu____3785 =
                                               FStar_ST.op_Bang tacdbg  in
                                             if uu____3785
                                             then
                                               let uu____3809 =
                                                 FStar_Common.string_of_list
                                                   (fun imp  ->
                                                      FStar_Syntax_Print.ctx_uvar_to_string
                                                        imp.FStar_TypeChecker_Env.imp_uvar)
                                                   ps1.FStar_Tactics_Types.all_implicits
                                                  in
                                               FStar_Util.print1
                                                 "Checked (2) implicits: %s\n"
                                                 uu____3809
                                             else ());
                                            report_implicits ps1
                                              g3.FStar_TypeChecker_Env.implicits;
                                            ((FStar_List.append
                                                ps1.FStar_Tactics_Types.goals
                                                ps1.FStar_Tactics_Types.smt_goals),
                                              w))))
                                     | FStar_Tactics_Result.Failed (s,ps1) ->
                                         ((let uu____3819 =
                                             let uu____3820 =
                                               FStar_TypeChecker_Normalize.psc_subst
                                                 ps1.FStar_Tactics_Types.psc
                                                in
                                             FStar_Tactics_Types.subst_proof_state
                                               uu____3820 ps1
                                              in
                                           FStar_Tactics_Basic.dump_proofstate
                                             uu____3819
                                             "at the time of failure");
                                          (let uu____3821 =
                                             let uu____3826 =
                                               FStar_Util.format1
                                                 "user tactic failed: %s" s
                                                in
                                             (FStar_Errors.Fatal_UserTacticFailure,
                                               uu____3826)
                                              in
                                           FStar_Errors.raise_error
                                             uu____3821
                                             ps1.FStar_Tactics_Types.entry_range)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____3838 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____3844 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____3850 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3905 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3945 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3999 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____4040 . 'Auu____4040 -> 'Auu____4040 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____4068 = FStar_Syntax_Util.head_and_args t  in
        match uu____4068 with
        | (hd1,args) ->
            let uu____4111 =
              let uu____4126 =
                let uu____4127 = FStar_Syntax_Util.un_uinst hd1  in
                uu____4127.FStar_Syntax_Syntax.n  in
              (uu____4126, args)  in
            (match uu____4111 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____4142))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____4205 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____4205 with
                       | (gs,uu____4213) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____4220 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____4220 with
                       | (gs,uu____4228) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____4271 =
                        let uu____4278 =
                          let uu____4281 =
                            let uu____4282 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____4282
                             in
                          [uu____4281]  in
                        (FStar_Syntax_Util.t_true, uu____4278)  in
                      Simplified uu____4271
                  | Both  ->
                      let uu____4293 =
                        let uu____4302 =
                          let uu____4305 =
                            let uu____4306 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____4306
                             in
                          [uu____4305]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____4302)  in
                      Dual uu____4293
                  | Neg  -> Simplified (assertion, []))
             | uu____4319 -> Unchanged t)
  
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
    fun uu___338_4409  ->
      match uu___338_4409 with
      | Unchanged t -> let uu____4415 = f t  in Unchanged uu____4415
      | Simplified (t,gs) ->
          let uu____4422 = let uu____4429 = f t  in (uu____4429, gs)  in
          Simplified uu____4422
      | Dual (tn,tp,gs) ->
          let uu____4439 =
            let uu____4448 = f tn  in
            let uu____4449 = f tp  in (uu____4448, uu____4449, gs)  in
          Dual uu____4439
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____4512 = f t1 t2  in Unchanged uu____4512
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____4524 = let uu____4531 = f t1 t2  in (uu____4531, gs)
               in
            Simplified uu____4524
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____4545 = let uu____4552 = f t1 t2  in (uu____4552, gs)
               in
            Simplified uu____4545
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____4571 =
              let uu____4578 = f t1 t2  in
              (uu____4578, (FStar_List.append gs1 gs2))  in
            Simplified uu____4571
        | uu____4581 ->
            let uu____4590 = explode x  in
            (match uu____4590 with
             | (n1,p1,gs1) ->
                 let uu____4608 = explode y  in
                 (match uu____4608 with
                  | (n2,p2,gs2) ->
                      let uu____4626 =
                        let uu____4635 = f n1 n2  in
                        let uu____4636 = f p1 p2  in
                        (uu____4635, uu____4636, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____4626))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____4708 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____4708
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____4756  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____4798 =
              let uu____4799 = FStar_Syntax_Subst.compress t  in
              uu____4799.FStar_Syntax_Syntax.n  in
            match uu____4798 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____4811 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____4811 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____4837 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____4837 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4857;
                   FStar_Syntax_Syntax.vars = uu____4858;_},(p,uu____4860)::
                 (q,uu____4862)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____4918 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4918
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____4921 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____4921 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4935 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4935.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4939;
                   FStar_Syntax_Syntax.vars = uu____4940;_},(p,uu____4942)::
                 (q,uu____4944)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____5000 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5000
                   in
                let xq =
                  let uu____5002 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5002
                   in
                let r1 =
                  let uu____5004 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____5004 p  in
                let r2 =
                  let uu____5006 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____5006 q  in
                (match (r1, r2) with
                 | (Unchanged uu____5013,Unchanged uu____5014) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____5032 = FStar_Syntax_Util.mk_iff l r  in
                            uu____5032.FStar_Syntax_Syntax.n) r1 r2
                 | uu____5035 ->
                     let uu____5044 = explode r1  in
                     (match uu____5044 with
                      | (pn,pp,gs1) ->
                          let uu____5062 = explode r2  in
                          (match uu____5062 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____5083 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____5086 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____5083
                                   uu____5086
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____5150  ->
                       fun r  ->
                         match uu____5150 with
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
                let uu____5302 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____5302 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____5342  ->
                            match uu____5342 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____5364 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___342_5396 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___342_5396.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___342_5396.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____5364 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____5424 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____5424.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____5470 = traverse f pol e t1  in
                let uu____5475 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____5475 uu____5470
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___343_5515 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___343_5515.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___343_5515.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____5522 =
                f pol e
                  (let uu___344_5526 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___344_5526.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___344_5526.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____5522
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___345_5536 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___345_5536.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___345_5536.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____5537 = explode rp  in
              (match uu____5537 with
               | (uu____5546,p',gs') ->
                   Dual
                     ((let uu___346_5556 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___346_5556.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___346_5556.FStar_Syntax_Syntax.vars)
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
      (let uu____5599 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5599);
      (let uu____5624 = FStar_ST.op_Bang tacdbg  in
       if uu____5624
       then
         let uu____5648 =
           let uu____5649 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____5649
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____5650 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____5648
           uu____5650
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____5679 =
         let uu____5688 = traverse by_tactic_interp Pos env goal  in
         match uu____5688 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____5712 -> failwith "no"  in
       match uu____5679 with
       | (t',gs) ->
           ((let uu____5740 = FStar_ST.op_Bang tacdbg  in
             if uu____5740
             then
               let uu____5764 =
                 let uu____5765 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____5765
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____5766 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____5764 uu____5766
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5814  ->
                    fun g  ->
                      match uu____5814 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5859 =
                              let uu____5862 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____5863 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____5862 uu____5863  in
                            match uu____5859 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5864 =
                                  let uu____5869 =
                                    let uu____5870 =
                                      let uu____5871 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____5871
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5870
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5869)
                                   in
                                FStar_Errors.raise_error uu____5864
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5874 = FStar_ST.op_Bang tacdbg  in
                            if uu____5874
                            then
                              let uu____5898 = FStar_Util.string_of_int n1
                                 in
                              let uu____5899 =
                                let uu____5900 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____5900
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5898 uu____5899
                            else ());
                           (let gt' =
                              let uu____5903 =
                                let uu____5904 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____5904
                                 in
                              FStar_TypeChecker_Util.label uu____5903
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____5905 =
                              let uu____5914 =
                                let uu____5921 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____5921, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____5914 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____5905)))) s
                 gs
                in
             let uu____5936 = s1  in
             match uu____5936 with
             | (uu____5957,gs1) ->
                 let uu____5975 =
                   let uu____5982 = FStar_Options.peek ()  in
                   (env, t', uu____5982)  in
                 uu____5975 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____5995 =
        let uu____5996 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____5996  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____5995 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____5997 =
      let uu____6002 =
        let uu____6003 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____6012 =
          let uu____6023 = FStar_Syntax_Syntax.as_arg a  in [uu____6023]  in
        uu____6003 :: uu____6012  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____6002  in
    uu____5997 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
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
          let uu____6073 =
            let uu____6078 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____6079 =
              let uu____6080 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6080]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____6078 uu____6079  in
          uu____6073 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____6109 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____6109);
           (let uu____6133 =
              let uu____6140 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____6140 env typ
               in
            match uu____6133 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____6154 =
                        let uu____6157 = FStar_Tactics_Types.goal_env g  in
                        let uu____6158 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____6157 uu____6158  in
                      match uu____6154 with
                      | FStar_Pervasives_Native.Some vc ->
                          let guard =
                            {
                              FStar_TypeChecker_Env.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Env.deferred = [];
                              FStar_TypeChecker_Env.univ_ineqs = ([], []);
                              FStar_TypeChecker_Env.implicits = []
                            }  in
                          let uu____6169 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____6169 guard
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
      (let uu____6185 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____6185);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____6210 =
         let uu____6217 = reify_tactic tau  in
         run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
           tau.FStar_Syntax_Syntax.pos uu____6217 env typ
          in
       match uu____6210 with
       | (gs,w) ->
           ((let uu____6227 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____6231 =
                      let uu____6232 =
                        let uu____6235 = FStar_Tactics_Types.goal_env g  in
                        let uu____6236 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____6235 uu____6236  in
                      FStar_Option.isSome uu____6232  in
                    Prims.op_Negation uu____6231) gs
                in
             if uu____6227
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
             let uu____6239 =
               let uu____6244 =
                 FStar_Syntax_Embeddings.e_list
                   FStar_Reflection_Embeddings.e_sigelt
                  in
               FStar_Syntax_Embeddings.unembed uu____6244 w1  in
             match uu____6239 with
             | FStar_Pervasives_Native.Some sigelts -> sigelts
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SpliceUnembedFail,
                     "splice: failed to unembed sigelts")
                   typ.FStar_Syntax_Syntax.pos)))
  