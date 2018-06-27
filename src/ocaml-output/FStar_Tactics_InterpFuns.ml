open Prims
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
              | (embedded_state,uu____57)::[] ->
                  let uu____82 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Tactics_Embedding.e_proofstate embedded_state
                     in
                  FStar_Util.bind_opt uu____82
                    (fun ps  ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       FStar_Tactics_Basic.log ps1
                         (fun uu____95  ->
                            let uu____96 = FStar_Ident.string_of_lid nm  in
                            let uu____97 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____96 uu____97);
                       (let res =
                          let uu____99 = FStar_Tactics_Embedding.e_result er
                             in
                          let uu____104 =
                            FStar_TypeChecker_Normalize.psc_range psc  in
                          let uu____105 = FStar_Tactics_Basic.run_safe t ps1
                             in
                          FStar_Syntax_Embeddings.embed uu____99 uu____104
                            uu____105
                           in
                        FStar_Pervasives_Native.Some res))
              | uu____110 ->
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
                | (a,uu____188)::(embedded_state,uu____190)::[] ->
                    let uu____231 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state
                       in
                    FStar_Util.bind_opt uu____231
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____244  ->
                              let uu____245 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____246 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____245 uu____246);
                         (let uu____247 =
                            FStar_Syntax_Embeddings.unembed ea a  in
                          FStar_Util.bind_opt uu____247
                            (fun a1  ->
                               let res =
                                 let uu____257 = t a1  in
                                 FStar_Tactics_Basic.run_safe uu____257 ps1
                                  in
                               let uu____260 =
                                 let uu____261 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____266 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 FStar_Syntax_Embeddings.embed uu____261
                                   uu____266 res
                                  in
                               FStar_Pervasives_Native.Some uu____260)))
                | uu____269 ->
                    let uu____270 =
                      let uu____271 = FStar_Ident.string_of_lid nm  in
                      let uu____272 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____271 uu____272
                       in
                    failwith uu____270
  
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
                | (a,uu____355)::(embedded_state,uu____357)::[] ->
                    let uu____398 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state
                       in
                    FStar_Util.bind_opt uu____398
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____411  ->
                              let uu____412 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____413 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____412 uu____413);
                         (let uu____414 =
                            FStar_Syntax_Embeddings.unembed ea a  in
                          FStar_Util.bind_opt uu____414
                            (fun a1  ->
                               let res =
                                 let uu____424 = t psc a1  in
                                 FStar_Tactics_Basic.run_safe uu____424 ps1
                                  in
                               let uu____427 =
                                 let uu____428 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____433 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 FStar_Syntax_Embeddings.embed uu____428
                                   uu____433 res
                                  in
                               FStar_Pervasives_Native.Some uu____427)))
                | uu____436 ->
                    let uu____437 =
                      let uu____438 = FStar_Ident.string_of_lid nm  in
                      let uu____439 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____438 uu____439
                       in
                    failwith uu____437
  
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
                  | (a,uu____536)::(b,uu____538)::(embedded_state,uu____540)::[]
                      ->
                      let uu____597 =
                        FStar_Syntax_Embeddings.unembed
                          FStar_Tactics_Embedding.e_proofstate embedded_state
                         in
                      FStar_Util.bind_opt uu____597
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____610  ->
                                let uu____611 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____612 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____611
                                  uu____612);
                           (let uu____613 =
                              FStar_Syntax_Embeddings.unembed ea a  in
                            FStar_Util.bind_opt uu____613
                              (fun a1  ->
                                 let uu____619 =
                                   FStar_Syntax_Embeddings.unembed eb b  in
                                 FStar_Util.bind_opt uu____619
                                   (fun b1  ->
                                      let res =
                                        let uu____629 = t a1 b1  in
                                        FStar_Tactics_Basic.run_safe
                                          uu____629 ps1
                                         in
                                      let uu____632 =
                                        let uu____633 =
                                          FStar_Tactics_Embedding.e_result er
                                           in
                                        let uu____638 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc
                                           in
                                        FStar_Syntax_Embeddings.embed
                                          uu____633 uu____638 res
                                         in
                                      FStar_Pervasives_Native.Some uu____632))))
                  | uu____641 ->
                      let uu____642 =
                        let uu____643 = FStar_Ident.string_of_lid nm  in
                        let uu____644 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____643 uu____644
                         in
                      failwith uu____642
  
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
                    | (a,uu____760)::(b,uu____762)::(c,uu____764)::(embedded_state,uu____766)::[]
                        ->
                        let uu____839 =
                          FStar_Syntax_Embeddings.unembed
                            FStar_Tactics_Embedding.e_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____839
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____852  ->
                                  let uu____853 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____854 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____853
                                    uu____854);
                             (let uu____855 =
                                FStar_Syntax_Embeddings.unembed ea a  in
                              FStar_Util.bind_opt uu____855
                                (fun a1  ->
                                   let uu____861 =
                                     FStar_Syntax_Embeddings.unembed eb b  in
                                   FStar_Util.bind_opt uu____861
                                     (fun b1  ->
                                        let uu____867 =
                                          FStar_Syntax_Embeddings.unembed ec
                                            c
                                           in
                                        FStar_Util.bind_opt uu____867
                                          (fun c1  ->
                                             let res =
                                               let uu____877 = t a1 b1 c1  in
                                               FStar_Tactics_Basic.run_safe
                                                 uu____877 ps1
                                                in
                                             let uu____880 =
                                               let uu____881 =
                                                 FStar_Tactics_Embedding.e_result
                                                   er
                                                  in
                                               let uu____886 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc
                                                  in
                                               FStar_Syntax_Embeddings.embed
                                                 uu____881 uu____886 res
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____880)))))
                    | uu____889 ->
                        let uu____890 =
                          let uu____891 = FStar_Ident.string_of_lid nm  in
                          let uu____892 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____891 uu____892
                           in
                        failwith uu____890
  
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
                      | (a,uu____1027)::(b,uu____1029)::(c,uu____1031)::
                          (d,uu____1033)::(embedded_state,uu____1035)::[] ->
                          let uu____1124 =
                            FStar_Syntax_Embeddings.unembed
                              FStar_Tactics_Embedding.e_proofstate
                              embedded_state
                             in
                          FStar_Util.bind_opt uu____1124
                            (fun ps  ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____1137  ->
                                    let uu____1138 =
                                      FStar_Ident.string_of_lid nm  in
                                    let uu____1139 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state
                                       in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n"
                                      uu____1138 uu____1139);
                               (let uu____1140 =
                                  FStar_Syntax_Embeddings.unembed ea a  in
                                FStar_Util.bind_opt uu____1140
                                  (fun a1  ->
                                     let uu____1146 =
                                       FStar_Syntax_Embeddings.unembed eb b
                                        in
                                     FStar_Util.bind_opt uu____1146
                                       (fun b1  ->
                                          let uu____1152 =
                                            FStar_Syntax_Embeddings.unembed
                                              ec c
                                             in
                                          FStar_Util.bind_opt uu____1152
                                            (fun c1  ->
                                               let uu____1158 =
                                                 FStar_Syntax_Embeddings.unembed
                                                   ed d
                                                  in
                                               FStar_Util.bind_opt uu____1158
                                                 (fun d1  ->
                                                    let res =
                                                      let uu____1168 =
                                                        t a1 b1 c1 d1  in
                                                      FStar_Tactics_Basic.run_safe
                                                        uu____1168 ps1
                                                       in
                                                    let uu____1171 =
                                                      let uu____1172 =
                                                        FStar_Tactics_Embedding.e_result
                                                          er
                                                         in
                                                      let uu____1177 =
                                                        FStar_TypeChecker_Normalize.psc_range
                                                          psc
                                                         in
                                                      FStar_Syntax_Embeddings.embed
                                                        uu____1172 uu____1177
                                                        res
                                                       in
                                                    FStar_Pervasives_Native.Some
                                                      uu____1171))))))
                      | uu____1180 ->
                          let uu____1181 =
                            let uu____1182 = FStar_Ident.string_of_lid nm  in
                            let uu____1183 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____1182 uu____1183
                             in
                          failwith uu____1181
  
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
                        | (a,uu____1337)::(b,uu____1339)::(c,uu____1341)::
                            (d,uu____1343)::(e,uu____1345)::(embedded_state,uu____1347)::[]
                            ->
                            let uu____1452 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Tactics_Embedding.e_proofstate
                                embedded_state
                               in
                            FStar_Util.bind_opt uu____1452
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1465  ->
                                      let uu____1466 =
                                        FStar_Ident.string_of_lid nm  in
                                      let uu____1467 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state
                                         in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1466 uu____1467);
                                 (let uu____1468 =
                                    FStar_Syntax_Embeddings.unembed ea a  in
                                  FStar_Util.bind_opt uu____1468
                                    (fun a1  ->
                                       let uu____1474 =
                                         FStar_Syntax_Embeddings.unembed eb b
                                          in
                                       FStar_Util.bind_opt uu____1474
                                         (fun b1  ->
                                            let uu____1480 =
                                              FStar_Syntax_Embeddings.unembed
                                                ec c
                                               in
                                            FStar_Util.bind_opt uu____1480
                                              (fun c1  ->
                                                 let uu____1486 =
                                                   FStar_Syntax_Embeddings.unembed
                                                     ed d
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____1486
                                                   (fun d1  ->
                                                      let uu____1492 =
                                                        FStar_Syntax_Embeddings.unembed
                                                          ee e
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____1492
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____1502 =
                                                               t a1 b1 c1 d1
                                                                 e1
                                                                in
                                                             FStar_Tactics_Basic.run_safe
                                                               uu____1502 ps1
                                                              in
                                                           let uu____1505 =
                                                             let uu____1506 =
                                                               FStar_Tactics_Embedding.e_result
                                                                 er
                                                                in
                                                             let uu____1511 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc
                                                                in
                                                             FStar_Syntax_Embeddings.embed
                                                               uu____1506
                                                               uu____1511 res
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1505)))))))
                        | uu____1514 ->
                            let uu____1515 =
                              let uu____1516 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____1517 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1516 uu____1517
                               in
                            failwith uu____1515
  
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
                          | (a,uu____1690)::(b,uu____1692)::(c,uu____1694)::
                              (d,uu____1696)::(e,uu____1698)::(f,uu____1700)::
                              (embedded_state,uu____1702)::[] ->
                              let uu____1823 =
                                FStar_Syntax_Embeddings.unembed
                                  FStar_Tactics_Embedding.e_proofstate
                                  embedded_state
                                 in
                              FStar_Util.bind_opt uu____1823
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1836  ->
                                        let uu____1837 =
                                          FStar_Ident.string_of_lid nm  in
                                        let uu____1838 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state
                                           in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1837 uu____1838);
                                   (let uu____1839 =
                                      FStar_Syntax_Embeddings.unembed ea a
                                       in
                                    FStar_Util.bind_opt uu____1839
                                      (fun a1  ->
                                         let uu____1845 =
                                           FStar_Syntax_Embeddings.unembed eb
                                             b
                                            in
                                         FStar_Util.bind_opt uu____1845
                                           (fun b1  ->
                                              let uu____1851 =
                                                FStar_Syntax_Embeddings.unembed
                                                  ec c
                                                 in
                                              FStar_Util.bind_opt uu____1851
                                                (fun c1  ->
                                                   let uu____1857 =
                                                     FStar_Syntax_Embeddings.unembed
                                                       ed d
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____1857
                                                     (fun d1  ->
                                                        let uu____1863 =
                                                          FStar_Syntax_Embeddings.unembed
                                                            ee e
                                                           in
                                                        FStar_Util.bind_opt
                                                          uu____1863
                                                          (fun e1  ->
                                                             let uu____1869 =
                                                               FStar_Syntax_Embeddings.unembed
                                                                 ef f
                                                                in
                                                             FStar_Util.bind_opt
                                                               uu____1869
                                                               (fun f1  ->
                                                                  let res =
                                                                    let uu____1879
                                                                    =
                                                                    t a1 b1
                                                                    c1 d1 e1
                                                                    f1  in
                                                                    FStar_Tactics_Basic.run_safe
                                                                    uu____1879
                                                                    ps1  in
                                                                  let uu____1882
                                                                    =
                                                                    let uu____1883
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                    let uu____1888
                                                                    =
                                                                    FStar_TypeChecker_Normalize.psc_range
                                                                    psc  in
                                                                    FStar_Syntax_Embeddings.embed
                                                                    uu____1883
                                                                    uu____1888
                                                                    res  in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____1882))))))))
                          | uu____1891 ->
                              let uu____1892 =
                                let uu____1893 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____1894 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1893 uu____1894
                                 in
                              failwith uu____1892
  
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
  
let (mk :
  Prims.string ->
    Prims.int ->
      (FStar_Ident.lid ->
         FStar_TypeChecker_Normalize.psc ->
           FStar_Syntax_Syntax.args ->
             FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
        -> FStar_TypeChecker_Normalize.primitive_step)
  =
  fun nm  ->
    fun arity  ->
      fun interpretation  ->
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
        }
  
let (native_tactics : FStar_Tactics_Native.native_primitive_step Prims.list)
  = FStar_Tactics_Native.list_all () 
let (native_tactics_steps :
  FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  FStar_List.map step_from_native_step native_tactics 
let mktac1 :
  'a 'r .
    Prims.string ->
      ('a -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_TypeChecker_Normalize.primitive_step
  =
  fun name  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          mk name (Prims.parse_int "2")
            (mk_tactic_interpretation_1 false f ea er)
  
let mktac2 :
  'a 'b 'r .
    Prims.string ->
      ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_TypeChecker_Normalize.primitive_step
  =
  fun name  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            mk name (Prims.parse_int "3")
              (mk_tactic_interpretation_2 false f ea eb er)
  
let mktac3 :
  'a 'b 'c 'r .
    Prims.string ->
      ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'c FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                FStar_TypeChecker_Normalize.primitive_step
  =
  fun name  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun er  ->
              mk name (Prims.parse_int "4")
                (mk_tactic_interpretation_3 false f ea eb ec er)
  
let mktac5 :
  'a 'b 'c 'd 'e 'r .
    Prims.string ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'c FStar_Syntax_Embeddings.embedding ->
              'd FStar_Syntax_Embeddings.embedding ->
                'e FStar_Syntax_Embeddings.embedding ->
                  'r FStar_Syntax_Embeddings.embedding ->
                    FStar_TypeChecker_Normalize.primitive_step
  =
  fun name  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun ed  ->
              fun ee  ->
                fun er  ->
                  mk name (Prims.parse_int "6")
                    (mk_tactic_interpretation_5 false f ea eb ec ed ee er)
  