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
              | (embedded_state,uu____57)::[] ->
                  let uu____74 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Tactics_Embedding.e_proofstate embedded_state
                     in
                  FStar_Util.bind_opt uu____74
                    (fun ps  ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       FStar_Tactics_Basic.log ps1
                         (fun uu____87  ->
                            let uu____88 = FStar_Ident.string_of_lid nm  in
                            let uu____89 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____88 uu____89);
                       (let res =
                          let uu____91 = FStar_Tactics_Embedding.e_result er
                             in
                          let uu____96 =
                            FStar_TypeChecker_Normalize.psc_range psc  in
                          let uu____97 = FStar_Tactics_Basic.run t ps1  in
                          FStar_Syntax_Embeddings.embed uu____91 uu____96
                            uu____97
                           in
                        FStar_Pervasives_Native.Some res))
              | uu____102 ->
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
                | (a,uu____164)::(embedded_state,uu____166)::[] ->
                    let uu____193 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state
                       in
                    FStar_Util.bind_opt uu____193
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____206  ->
                              let uu____207 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____208 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____207 uu____208);
                         (let uu____209 =
                            FStar_Syntax_Embeddings.unembed ea a  in
                          FStar_Util.bind_opt uu____209
                            (fun a1  ->
                               let res =
                                 let uu____219 = t a1  in
                                 FStar_Tactics_Basic.run uu____219 ps1  in
                               let uu____222 =
                                 let uu____223 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____228 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 FStar_Syntax_Embeddings.embed uu____223
                                   uu____228 res
                                  in
                               FStar_Pervasives_Native.Some uu____222)))
                | uu____231 ->
                    let uu____232 =
                      let uu____233 = FStar_Ident.string_of_lid nm  in
                      let uu____234 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____233 uu____234
                       in
                    failwith uu____232
  
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
                | (a,uu____301)::(embedded_state,uu____303)::[] ->
                    let uu____330 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state
                       in
                    FStar_Util.bind_opt uu____330
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____343  ->
                              let uu____344 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____345 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____344 uu____345);
                         (let uu____346 =
                            FStar_Syntax_Embeddings.unembed ea a  in
                          FStar_Util.bind_opt uu____346
                            (fun a1  ->
                               let res =
                                 let uu____356 = t psc a1  in
                                 FStar_Tactics_Basic.run uu____356 ps1  in
                               let uu____359 =
                                 let uu____360 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____365 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 FStar_Syntax_Embeddings.embed uu____360
                                   uu____365 res
                                  in
                               FStar_Pervasives_Native.Some uu____359)))
                | uu____368 ->
                    let uu____369 =
                      let uu____370 = FStar_Ident.string_of_lid nm  in
                      let uu____371 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____370 uu____371
                       in
                    failwith uu____369
  
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
                  | (a,uu____449)::(b,uu____451)::(embedded_state,uu____453)::[]
                      ->
                      let uu____490 =
                        FStar_Syntax_Embeddings.unembed
                          FStar_Tactics_Embedding.e_proofstate embedded_state
                         in
                      FStar_Util.bind_opt uu____490
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____503  ->
                                let uu____504 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____505 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____504
                                  uu____505);
                           (let uu____506 =
                              FStar_Syntax_Embeddings.unembed ea a  in
                            FStar_Util.bind_opt uu____506
                              (fun a1  ->
                                 let uu____512 =
                                   FStar_Syntax_Embeddings.unembed eb b  in
                                 FStar_Util.bind_opt uu____512
                                   (fun b1  ->
                                      let res =
                                        let uu____522 = t a1 b1  in
                                        FStar_Tactics_Basic.run uu____522 ps1
                                         in
                                      let uu____525 =
                                        let uu____526 =
                                          FStar_Tactics_Embedding.e_result er
                                           in
                                        let uu____531 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc
                                           in
                                        FStar_Syntax_Embeddings.embed
                                          uu____526 uu____531 res
                                         in
                                      FStar_Pervasives_Native.Some uu____525))))
                  | uu____534 ->
                      let uu____535 =
                        let uu____536 = FStar_Ident.string_of_lid nm  in
                        let uu____537 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____536 uu____537
                         in
                      failwith uu____535
  
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
                    | (a,uu____631)::(b,uu____633)::(c,uu____635)::(embedded_state,uu____637)::[]
                        ->
                        let uu____684 =
                          FStar_Syntax_Embeddings.unembed
                            FStar_Tactics_Embedding.e_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____684
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____697  ->
                                  let uu____698 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____699 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____698
                                    uu____699);
                             (let uu____700 =
                                FStar_Syntax_Embeddings.unembed ea a  in
                              FStar_Util.bind_opt uu____700
                                (fun a1  ->
                                   let uu____706 =
                                     FStar_Syntax_Embeddings.unembed eb b  in
                                   FStar_Util.bind_opt uu____706
                                     (fun b1  ->
                                        let uu____712 =
                                          FStar_Syntax_Embeddings.unembed ec
                                            c
                                           in
                                        FStar_Util.bind_opt uu____712
                                          (fun c1  ->
                                             let res =
                                               let uu____722 = t a1 b1 c1  in
                                               FStar_Tactics_Basic.run
                                                 uu____722 ps1
                                                in
                                             let uu____725 =
                                               let uu____726 =
                                                 FStar_Tactics_Embedding.e_result
                                                   er
                                                  in
                                               let uu____731 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc
                                                  in
                                               FStar_Syntax_Embeddings.embed
                                                 uu____726 uu____731 res
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____725)))))
                    | uu____734 ->
                        let uu____735 =
                          let uu____736 = FStar_Ident.string_of_lid nm  in
                          let uu____737 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____736 uu____737
                           in
                        failwith uu____735
  
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
                      | (a,uu____847)::(b,uu____849)::(c,uu____851)::
                          (d,uu____853)::(embedded_state,uu____855)::[] ->
                          let uu____912 =
                            FStar_Syntax_Embeddings.unembed
                              FStar_Tactics_Embedding.e_proofstate
                              embedded_state
                             in
                          FStar_Util.bind_opt uu____912
                            (fun ps  ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____925  ->
                                    let uu____926 =
                                      FStar_Ident.string_of_lid nm  in
                                    let uu____927 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state
                                       in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n" uu____926
                                      uu____927);
                               (let uu____928 =
                                  FStar_Syntax_Embeddings.unembed ea a  in
                                FStar_Util.bind_opt uu____928
                                  (fun a1  ->
                                     let uu____934 =
                                       FStar_Syntax_Embeddings.unembed eb b
                                        in
                                     FStar_Util.bind_opt uu____934
                                       (fun b1  ->
                                          let uu____940 =
                                            FStar_Syntax_Embeddings.unembed
                                              ec c
                                             in
                                          FStar_Util.bind_opt uu____940
                                            (fun c1  ->
                                               let uu____946 =
                                                 FStar_Syntax_Embeddings.unembed
                                                   ed d
                                                  in
                                               FStar_Util.bind_opt uu____946
                                                 (fun d1  ->
                                                    let res =
                                                      let uu____956 =
                                                        t a1 b1 c1 d1  in
                                                      FStar_Tactics_Basic.run
                                                        uu____956 ps1
                                                       in
                                                    let uu____959 =
                                                      let uu____960 =
                                                        FStar_Tactics_Embedding.e_result
                                                          er
                                                         in
                                                      let uu____965 =
                                                        FStar_TypeChecker_Normalize.psc_range
                                                          psc
                                                         in
                                                      FStar_Syntax_Embeddings.embed
                                                        uu____960 uu____965
                                                        res
                                                       in
                                                    FStar_Pervasives_Native.Some
                                                      uu____959))))))
                      | uu____968 ->
                          let uu____969 =
                            let uu____970 = FStar_Ident.string_of_lid nm  in
                            let uu____971 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____970 uu____971
                             in
                          failwith uu____969
  
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
                        | (a,uu____1097)::(b,uu____1099)::(c,uu____1101)::
                            (d,uu____1103)::(e,uu____1105)::(embedded_state,uu____1107)::[]
                            ->
                            let uu____1174 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Tactics_Embedding.e_proofstate
                                embedded_state
                               in
                            FStar_Util.bind_opt uu____1174
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1187  ->
                                      let uu____1188 =
                                        FStar_Ident.string_of_lid nm  in
                                      let uu____1189 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state
                                         in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1188 uu____1189);
                                 (let uu____1190 =
                                    FStar_Syntax_Embeddings.unembed ea a  in
                                  FStar_Util.bind_opt uu____1190
                                    (fun a1  ->
                                       let uu____1196 =
                                         FStar_Syntax_Embeddings.unembed eb b
                                          in
                                       FStar_Util.bind_opt uu____1196
                                         (fun b1  ->
                                            let uu____1202 =
                                              FStar_Syntax_Embeddings.unembed
                                                ec c
                                               in
                                            FStar_Util.bind_opt uu____1202
                                              (fun c1  ->
                                                 let uu____1208 =
                                                   FStar_Syntax_Embeddings.unembed
                                                     ed d
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____1208
                                                   (fun d1  ->
                                                      let uu____1214 =
                                                        FStar_Syntax_Embeddings.unembed
                                                          ee e
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____1214
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____1224 =
                                                               t a1 b1 c1 d1
                                                                 e1
                                                                in
                                                             FStar_Tactics_Basic.run
                                                               uu____1224 ps1
                                                              in
                                                           let uu____1227 =
                                                             let uu____1228 =
                                                               FStar_Tactics_Embedding.e_result
                                                                 er
                                                                in
                                                             let uu____1233 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc
                                                                in
                                                             FStar_Syntax_Embeddings.embed
                                                               uu____1228
                                                               uu____1233 res
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1227)))))))
                        | uu____1236 ->
                            let uu____1237 =
                              let uu____1238 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____1239 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1238 uu____1239
                               in
                            failwith uu____1237
  
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
                          | (a,uu____1381)::(b,uu____1383)::(c,uu____1385)::
                              (d,uu____1387)::(e,uu____1389)::(f,uu____1391)::
                              (embedded_state,uu____1393)::[] ->
                              let uu____1470 =
                                FStar_Syntax_Embeddings.unembed
                                  FStar_Tactics_Embedding.e_proofstate
                                  embedded_state
                                 in
                              FStar_Util.bind_opt uu____1470
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1483  ->
                                        let uu____1484 =
                                          FStar_Ident.string_of_lid nm  in
                                        let uu____1485 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state
                                           in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1484 uu____1485);
                                   (let uu____1486 =
                                      FStar_Syntax_Embeddings.unembed ea a
                                       in
                                    FStar_Util.bind_opt uu____1486
                                      (fun a1  ->
                                         let uu____1492 =
                                           FStar_Syntax_Embeddings.unembed eb
                                             b
                                            in
                                         FStar_Util.bind_opt uu____1492
                                           (fun b1  ->
                                              let uu____1498 =
                                                FStar_Syntax_Embeddings.unembed
                                                  ec c
                                                 in
                                              FStar_Util.bind_opt uu____1498
                                                (fun c1  ->
                                                   let uu____1504 =
                                                     FStar_Syntax_Embeddings.unembed
                                                       ed d
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____1504
                                                     (fun d1  ->
                                                        let uu____1510 =
                                                          FStar_Syntax_Embeddings.unembed
                                                            ee e
                                                           in
                                                        FStar_Util.bind_opt
                                                          uu____1510
                                                          (fun e1  ->
                                                             let uu____1516 =
                                                               FStar_Syntax_Embeddings.unembed
                                                                 ef f
                                                                in
                                                             FStar_Util.bind_opt
                                                               uu____1516
                                                               (fun f1  ->
                                                                  let res =
                                                                    let uu____1526
                                                                    =
                                                                    t a1 b1
                                                                    c1 d1 e1
                                                                    f1  in
                                                                    FStar_Tactics_Basic.run
                                                                    uu____1526
                                                                    ps1  in
                                                                  let uu____1529
                                                                    =
                                                                    let uu____1530
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                    let uu____1535
                                                                    =
                                                                    FStar_TypeChecker_Normalize.psc_range
                                                                    psc  in
                                                                    FStar_Syntax_Embeddings.embed
                                                                    uu____1530
                                                                    uu____1535
                                                                    res  in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____1529))))))))
                          | uu____1538 ->
                              let uu____1539 =
                                let uu____1540 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____1541 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1540 uu____1541
                                 in
                              failwith uu____1539
  
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
      (fun uu____1652  ->
         fun uu____1653  -> failwith "Impossible: embedding tactic (0)?")
      (fun w  ->
         fun t  ->
           let uu____1661 = unembed_tactic_0 er t  in
           FStar_All.pipe_left
             (fun _0_40  -> FStar_Pervasives_Native.Some _0_40) uu____1661)
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
        (fun uu____1684  ->
           fun uu____1685  -> failwith "Impossible: embedding tactic (1)?")
        (fun w  -> fun t  -> unembed_tactic_1 ea er t)
        FStar_Syntax_Syntax.t_unit

and (primitive_steps :
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____1694  ->
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
      | (ps,uu____1998)::[] ->
          let uu____2015 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2015
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2023 =
                 let uu____2024 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2025 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2024 uu____2025
                  in
               FStar_Pervasives_Native.Some uu____2023)
      | uu____2026 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____2030 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2030;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____2043)::[] ->
          let uu____2060 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2060
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2068 =
                 let uu____2069 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2070 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2069 uu____2070
                  in
               FStar_Pervasives_Native.Some uu____2068)
      | uu____2071 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____2075 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2075;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____2092)::[] ->
          let uu____2109 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2109
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2122 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2139)::(r,uu____2141)::[] ->
          let uu____2168 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____2168
            (fun ps1  ->
               let uu____2174 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_range r
                  in
               FStar_Util.bind_opt uu____2174
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2182 =
                      let uu____2183 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Syntax_Embeddings.embed
                        FStar_Tactics_Embedding.e_proofstate uu____2183 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2182))
      | uu____2184 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____2199)::(b,uu____2201)::[] ->
          let uu____2228 =
            FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_env
              env_t
             in
          FStar_Util.bind_opt uu____2228
            (fun env  ->
               let uu____2234 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Reflection_Embeddings.e_binder b
                  in
               FStar_Util.bind_opt uu____2234
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____2242 =
                      FStar_Syntax_Embeddings.embed
                        FStar_Reflection_Embeddings.e_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____2242))
      | uu____2243 -> failwith "Unexpected application of push_binder"  in
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
    let uu____2252 =
      let uu____2255 =
        mktac2 () () () "fail"
          (fun a427  ->
             fun a428  ->
               (Obj.magic (fun uu____2257  -> FStar_Tactics_Basic.fail)) a427
                 a428) (Obj.magic FStar_Syntax_Embeddings.e_any)
          (Obj.magic FStar_Syntax_Embeddings.e_string)
          (Obj.magic FStar_Syntax_Embeddings.e_any)
         in
      let uu____2258 =
        let uu____2261 =
          mktac1 () () "trivial"
            (fun a429  -> (Obj.magic FStar_Tactics_Basic.trivial) a429)
            (Obj.magic FStar_Syntax_Embeddings.e_unit)
            (Obj.magic FStar_Syntax_Embeddings.e_unit)
           in
        let uu____2262 =
          let uu____2265 =
            let uu____2266 = e_tactic_0' FStar_Syntax_Embeddings.e_any  in
            let uu____2271 =
              FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any
               in
            mktac2 () () () "__trytac"
              (fun a430  ->
                 fun a431  ->
                   (Obj.magic (fun uu____2277  -> FStar_Tactics_Basic.trytac))
                     a430 a431) (Obj.magic FStar_Syntax_Embeddings.e_any)
              (Obj.magic uu____2266) (Obj.magic uu____2271)
             in
          let uu____2278 =
            let uu____2281 =
              mktac1 () () "intro"
                (fun a432  -> (Obj.magic FStar_Tactics_Basic.intro) a432)
                (Obj.magic FStar_Syntax_Embeddings.e_unit)
                (Obj.magic FStar_Reflection_Embeddings.e_binder)
               in
            let uu____2282 =
              let uu____2285 =
                let uu____2286 =
                  FStar_Syntax_Embeddings.e_tuple2
                    FStar_Reflection_Embeddings.e_binder
                    FStar_Reflection_Embeddings.e_binder
                   in
                mktac1 () () "intro_rec"
                  (fun a433  ->
                     (Obj.magic FStar_Tactics_Basic.intro_rec) a433)
                  (Obj.magic FStar_Syntax_Embeddings.e_unit)
                  (Obj.magic uu____2286)
                 in
              let uu____2293 =
                let uu____2296 =
                  let uu____2297 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Syntax_Embeddings.e_norm_step
                     in
                  mktac1 () () "norm"
                    (fun a434  -> (Obj.magic FStar_Tactics_Basic.norm) a434)
                    (Obj.magic uu____2297)
                    (Obj.magic FStar_Syntax_Embeddings.e_unit)
                   in
                let uu____2302 =
                  let uu____2305 =
                    let uu____2306 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_norm_step
                       in
                    mktac3 () () () () "norm_term_env"
                      (fun a435  ->
                         fun a436  ->
                           fun a437  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a435 a436 a437)
                      (Obj.magic FStar_Reflection_Embeddings.e_env)
                      (Obj.magic uu____2306)
                      (Obj.magic FStar_Reflection_Embeddings.e_term)
                      (Obj.magic FStar_Reflection_Embeddings.e_term)
                     in
                  let uu____2311 =
                    let uu____2314 =
                      let uu____2315 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step
                         in
                      mktac2 () () () "norm_binder_type"
                        (fun a438  ->
                           fun a439  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a438 a439) (Obj.magic uu____2315)
                        (Obj.magic FStar_Reflection_Embeddings.e_binder)
                        (Obj.magic FStar_Syntax_Embeddings.e_unit)
                       in
                    let uu____2320 =
                      let uu____2323 =
                        mktac2 () () () "rename_to"
                          (fun a440  ->
                             fun a441  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a440
                                 a441)
                          (Obj.magic FStar_Reflection_Embeddings.e_binder)
                          (Obj.magic FStar_Syntax_Embeddings.e_string)
                          (Obj.magic FStar_Syntax_Embeddings.e_unit)
                         in
                      let uu____2324 =
                        let uu____2327 =
                          mktac1 () () "binder_retype"
                            (fun a442  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a442)
                            (Obj.magic FStar_Reflection_Embeddings.e_binder)
                            (Obj.magic FStar_Syntax_Embeddings.e_unit)
                           in
                        let uu____2328 =
                          let uu____2331 =
                            mktac1 () () "revert"
                              (fun a443  ->
                                 (Obj.magic FStar_Tactics_Basic.revert) a443)
                              (Obj.magic FStar_Syntax_Embeddings.e_unit)
                              (Obj.magic FStar_Syntax_Embeddings.e_unit)
                             in
                          let uu____2332 =
                            let uu____2335 =
                              mktac1 () () "clear_top"
                                (fun a444  ->
                                   (Obj.magic FStar_Tactics_Basic.clear_top)
                                     a444)
                                (Obj.magic FStar_Syntax_Embeddings.e_unit)
                                (Obj.magic FStar_Syntax_Embeddings.e_unit)
                               in
                            let uu____2336 =
                              let uu____2339 =
                                mktac1 () () "clear"
                                  (fun a445  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a445)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.e_binder)
                                  (Obj.magic FStar_Syntax_Embeddings.e_unit)
                                 in
                              let uu____2340 =
                                let uu____2343 =
                                  mktac1 () () "rewrite"
                                    (fun a446  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a446)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.e_binder)
                                    (Obj.magic FStar_Syntax_Embeddings.e_unit)
                                   in
                                let uu____2344 =
                                  let uu____2347 =
                                    mktac1 () () "smt"
                                      (fun a447  ->
                                         (Obj.magic FStar_Tactics_Basic.smt)
                                           a447)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.e_unit)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.e_unit)
                                     in
                                  let uu____2348 =
                                    let uu____2351 =
                                      mktac1 () () "refine_intro"
                                        (fun a448  ->
                                           (Obj.magic
                                              FStar_Tactics_Basic.refine_intro)
                                             a448)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.e_unit)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.e_unit)
                                       in
                                    let uu____2352 =
                                      let uu____2355 =
                                        mktac2 () () () "t_exact"
                                          (fun a449  ->
                                             fun a450  ->
                                               (Obj.magic
                                                  FStar_Tactics_Basic.t_exact)
                                                 a449 a450)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.e_bool)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.e_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.e_unit)
                                         in
                                      let uu____2356 =
                                        let uu____2359 =
                                          mktac1 () () "apply"
                                            (fun a451  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a451)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.e_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.e_unit)
                                           in
                                        let uu____2360 =
                                          let uu____2363 =
                                            mktac1 () () "apply_raw"
                                              (fun a452  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a452)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.e_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.e_unit)
                                             in
                                          let uu____2364 =
                                            let uu____2367 =
                                              mktac1 () () "apply_lemma"
                                                (fun a453  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a453)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.e_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.e_unit)
                                               in
                                            let uu____2368 =
                                              let uu____2371 =
                                                let uu____2372 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____2377 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____2382 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Syntax_Embeddings.e_any
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a454  ->
                                                     fun a455  ->
                                                       fun a456  ->
                                                         fun a457  ->
                                                           fun a458  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2391
                                                                    ->
                                                                   fun
                                                                    uu____2392
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a454 a455 a456
                                                               a457 a458)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.e_any)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.e_any)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.e_int)
                                                  (Obj.magic uu____2372)
                                                  (Obj.magic uu____2377)
                                                  (Obj.magic uu____2382)
                                                 in
                                              let uu____2393 =
                                                let uu____2396 =
                                                  let uu____2397 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____2402 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  mktac2 () () () "__seq"
                                                    (fun a459  ->
                                                       fun a460  ->
                                                         (Obj.magic
                                                            FStar_Tactics_Basic.seq)
                                                           a459 a460)
                                                    (Obj.magic uu____2397)
                                                    (Obj.magic uu____2402)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.e_unit)
                                                   in
                                                let uu____2407 =
                                                  let uu____2410 =
                                                    mktac1 () ()
                                                      "set_options"
                                                      (fun a461  ->
                                                         (Obj.magic
                                                            FStar_Tactics_Basic.set_options)
                                                           a461)
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.e_string)
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.e_unit)
                                                     in
                                                  let uu____2411 =
                                                    let uu____2414 =
                                                      mktac1 () () "tc"
                                                        (fun a462  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a462)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.e_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.e_term)
                                                       in
                                                    let uu____2415 =
                                                      let uu____2418 =
                                                        mktac1 () ()
                                                          "unshelve"
                                                          (fun a463  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a463)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.e_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.e_unit)
                                                         in
                                                      let uu____2419 =
                                                        let uu____2422 =
                                                          mktac2 () () ()
                                                            "unquote"
                                                            (fun a464  ->
                                                               fun a465  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a464 a465)
                                                            (Obj.magic
                                                               FStar_Syntax_Embeddings.e_any)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.e_term)
                                                            (Obj.magic
                                                               FStar_Syntax_Embeddings.e_any)
                                                           in
                                                        let uu____2423 =
                                                          let uu____2426 =
                                                            mktac1 () ()
                                                              "prune"
                                                              (fun a466  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a466)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.e_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.e_unit)
                                                             in
                                                          let uu____2427 =
                                                            let uu____2430 =
                                                              mktac1 () ()
                                                                "addns"
                                                                (fun a467  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a467)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_unit)
                                                               in
                                                            let uu____2431 =
                                                              let uu____2434
                                                                =
                                                                mktac1 () ()
                                                                  "print"
                                                                  (fun a468 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print)
                                                                    a468)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                 in
                                                              let uu____2435
                                                                =
                                                                let uu____2438
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "debug"
                                                                    (
                                                                    fun a469 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.debug)
                                                                    a469)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                   in
                                                                let uu____2439
                                                                  =
                                                                  let uu____2442
                                                                    =
                                                                    mktac1 ()
                                                                    () "dump"
                                                                    (fun a470
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a470)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                  let uu____2443
                                                                    =
                                                                    let uu____2446
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "dump1"
                                                                    (fun a471
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a471)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2447
                                                                    =
                                                                    let uu____2450
                                                                    =
                                                                    let uu____2451
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a472
                                                                     ->
                                                                    fun a473 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a472 a473)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.e_direction)
                                                                    (Obj.magic
                                                                    uu____2451)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2456
                                                                    =
                                                                    let uu____2459
                                                                    =
                                                                    let uu____2460
                                                                    =
                                                                    let uu____2471
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____2471
                                                                     in
                                                                    let uu____2482
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__topdown_rewrite"
                                                                    (fun a474
                                                                     ->
                                                                    fun a475 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.topdown_rewrite)
                                                                    a474 a475)
                                                                    (Obj.magic
                                                                    uu____2460)
                                                                    (Obj.magic
                                                                    uu____2482)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2487
                                                                    =
                                                                    let uu____2490
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "trefl"
                                                                    (fun a476
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    a476)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2491
                                                                    =
                                                                    let uu____2494
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "later"
                                                                    (fun a477
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    a477)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2495
                                                                    =
                                                                    let uu____2498
                                                                    =
                                                                    mktac1 ()
                                                                    () "dup"
                                                                    (fun a478
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    a478)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2499
                                                                    =
                                                                    let uu____2502
                                                                    =
                                                                    mktac1 ()
                                                                    () "flip"
                                                                    (fun a479
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    a479)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2503
                                                                    =
                                                                    let uu____2506
                                                                    =
                                                                    mktac1 ()
                                                                    () "qed"
                                                                    (fun a480
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    a480)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2507
                                                                    =
                                                                    let uu____2510
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "dismiss"
                                                                    (fun a481
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dismiss)
                                                                    a481)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2511
                                                                    =
                                                                    let uu____2514
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "tadmit"
                                                                    (fun a482
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.tadmit)
                                                                    a482)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2515
                                                                    =
                                                                    let uu____2518
                                                                    =
                                                                    let uu____2519
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "cases"
                                                                    (fun a483
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a483)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    uu____2519)
                                                                     in
                                                                    let uu____2526
                                                                    =
                                                                    let uu____2529
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "top_env"
                                                                    (fun a484
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    a484)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_env)
                                                                     in
                                                                    let uu____2530
                                                                    =
                                                                    let uu____2533
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_env"
                                                                    (fun a485
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    a485)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_env)
                                                                     in
                                                                    let uu____2534
                                                                    =
                                                                    let uu____2537
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_goal"
                                                                    (fun a486
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    a486)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                     in
                                                                    let uu____2538
                                                                    =
                                                                    let uu____2541
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "cur_witness"
                                                                    (fun a487
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    a487)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                     in
                                                                    let uu____2542
                                                                    =
                                                                    let uu____2545
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "inspect"
                                                                    (fun a488
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.inspect)
                                                                    a488)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term_view)
                                                                     in
                                                                    let uu____2546
                                                                    =
                                                                    let uu____2549
                                                                    =
                                                                    mktac1 ()
                                                                    () "pack"
                                                                    (fun a489
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pack)
                                                                    a489)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term_view)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                     in
                                                                    let uu____2550
                                                                    =
                                                                    let uu____2553
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "fresh"
                                                                    (fun a490
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh)
                                                                    a490)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_int)
                                                                     in
                                                                    let uu____2554
                                                                    =
                                                                    let uu____2557
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "ngoals"
                                                                    (fun a491
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals)
                                                                    a491)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_int)
                                                                     in
                                                                    let uu____2558
                                                                    =
                                                                    let uu____2561
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "ngoals_smt"
                                                                    (fun a492
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals_smt)
                                                                    a492)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_int)
                                                                     in
                                                                    let uu____2562
                                                                    =
                                                                    let uu____2565
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "is_guard"
                                                                    (fun a493
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    a493)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_bool)
                                                                     in
                                                                    let uu____2566
                                                                    =
                                                                    let uu____2569
                                                                    =
                                                                    let uu____2570
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "uvar_env"
                                                                    (fun a494
                                                                     ->
                                                                    fun a495 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a494 a495)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_env)
                                                                    (Obj.magic
                                                                    uu____2570)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                     in
                                                                    let uu____2575
                                                                    =
                                                                    let uu____2578
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "unify"
                                                                    (fun a496
                                                                     ->
                                                                    fun a497 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a496 a497)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_bool)
                                                                     in
                                                                    let uu____2579
                                                                    =
                                                                    let uu____2582
                                                                    =
                                                                    let uu____2583
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "launch_process"
                                                                    (fun a498
                                                                     ->
                                                                    fun a499 
                                                                    ->
                                                                    fun a500 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a498 a499
                                                                    a500)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    uu____2583)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                     in
                                                                    let uu____2588
                                                                    =
                                                                    let uu____2591
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "fresh_bv_named"
                                                                    (fun a501
                                                                     ->
                                                                    fun a502 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_bv_named)
                                                                    a501 a502)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_bv)
                                                                     in
                                                                    let uu____2592
                                                                    =
                                                                    let uu____2595
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "change"
                                                                    (fun a503
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.change)
                                                                    a503)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.e_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    let uu____2596
                                                                    =
                                                                    let uu____2599
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "get_guard_policy"
                                                                    (fun a504
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.get_guard_policy)
                                                                    a504)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.e_guard_policy)
                                                                     in
                                                                    let uu____2600
                                                                    =
                                                                    let uu____2603
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "set_guard_policy"
                                                                    (fun a505
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.set_guard_policy)
                                                                    a505)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.e_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                     in
                                                                    [uu____2603;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
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
                                                                    uu____2582
                                                                    ::
                                                                    uu____2588
                                                                     in
                                                                    uu____2578
                                                                    ::
                                                                    uu____2579
                                                                     in
                                                                    uu____2569
                                                                    ::
                                                                    uu____2575
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
                                                                    uu____2541
                                                                    ::
                                                                    uu____2542
                                                                     in
                                                                    uu____2537
                                                                    ::
                                                                    uu____2538
                                                                     in
                                                                    uu____2533
                                                                    ::
                                                                    uu____2534
                                                                     in
                                                                    uu____2529
                                                                    ::
                                                                    uu____2530
                                                                     in
                                                                    uu____2518
                                                                    ::
                                                                    uu____2526
                                                                     in
                                                                    uu____2514
                                                                    ::
                                                                    uu____2515
                                                                     in
                                                                    uu____2510
                                                                    ::
                                                                    uu____2511
                                                                     in
                                                                    uu____2506
                                                                    ::
                                                                    uu____2507
                                                                     in
                                                                    uu____2502
                                                                    ::
                                                                    uu____2503
                                                                     in
                                                                    uu____2498
                                                                    ::
                                                                    uu____2499
                                                                     in
                                                                    uu____2494
                                                                    ::
                                                                    uu____2495
                                                                     in
                                                                    uu____2490
                                                                    ::
                                                                    uu____2491
                                                                     in
                                                                    uu____2459
                                                                    ::
                                                                    uu____2487
                                                                     in
                                                                    uu____2450
                                                                    ::
                                                                    uu____2456
                                                                     in
                                                                    uu____2446
                                                                    ::
                                                                    uu____2447
                                                                     in
                                                                  uu____2442
                                                                    ::
                                                                    uu____2443
                                                                   in
                                                                uu____2438 ::
                                                                  uu____2439
                                                                 in
                                                              uu____2434 ::
                                                                uu____2435
                                                               in
                                                            uu____2430 ::
                                                              uu____2431
                                                             in
                                                          uu____2426 ::
                                                            uu____2427
                                                           in
                                                        uu____2422 ::
                                                          uu____2423
                                                         in
                                                      uu____2418 ::
                                                        uu____2419
                                                       in
                                                    uu____2414 :: uu____2415
                                                     in
                                                  uu____2410 :: uu____2411
                                                   in
                                                uu____2396 :: uu____2407  in
                                              uu____2371 :: uu____2393  in
                                            uu____2367 :: uu____2368  in
                                          uu____2363 :: uu____2364  in
                                        uu____2359 :: uu____2360  in
                                      uu____2355 :: uu____2356  in
                                    uu____2351 :: uu____2352  in
                                  uu____2347 :: uu____2348  in
                                uu____2343 :: uu____2344  in
                              uu____2339 :: uu____2340  in
                            uu____2335 :: uu____2336  in
                          uu____2331 :: uu____2332  in
                        uu____2327 :: uu____2328  in
                      uu____2323 :: uu____2324  in
                    uu____2314 :: uu____2320  in
                  uu____2305 :: uu____2311  in
                uu____2296 :: uu____2302  in
              uu____2285 :: uu____2293  in
            uu____2281 :: uu____2282  in
          uu____2265 :: uu____2278  in
        uu____2261 :: uu____2262  in
      uu____2255 :: uu____2258  in
    FStar_List.append uu____2252
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
               let uu____2625 =
                 let uu____2626 =
                   let uu____2627 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____2627]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____2626  in
               uu____2625 FStar_Pervasives_Native.None rng  in
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
             let uu____2650 =
               let uu____2651 =
                 let uu____2652 =
                   let uu____2653 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2653  in
                 [uu____2652]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2651  in
             uu____2650 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____2660 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____2660
            then
              let uu____2661 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2661
            else ());
           (let result =
              let uu____2664 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2664 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____2668 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2668
             then
               let uu____2669 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2669
             else ());
            (let res =
               let uu____2676 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Syntax_Embeddings.unembed uu____2676 result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____2689 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2689
                   (fun uu____2693  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____2698 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2698
                   (fun uu____2702  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2705 =
                   let uu____2710 =
                     let uu____2711 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2711
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2710)  in
                 FStar_Errors.raise_error uu____2705
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      let uu____2718 = unembed_tactic_0 eb embedded_tac_b  in
      FStar_All.pipe_left (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
        uu____2718

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2770  ->
             match uu____2770 with
             | (r,uu____2790,uv,uu____2792,ty,rng) ->
                 let uu____2795 =
                   let uu____2796 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____2797 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2796 uu____2797 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2795, rng)) is
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
        (let uu____2846 = FStar_ST.op_Bang tacdbg  in
         if uu____2846
         then
           let uu____2866 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2866
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____2870 = FStar_ST.op_Bang tacdbg  in
          if uu____2870
          then
            let uu____2890 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2890
          else ());
         (let uu____2892 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____2892 with
          | (uu____2905,uu____2906,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic1  in
                let uu____2913 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____2913 with
                | (env1,uu____2927) ->
                    let env2 =
                      let uu___60_2933 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___60_2933.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___60_2933.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___60_2933.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___60_2933.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___60_2933.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___60_2933.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___60_2933.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___60_2933.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___60_2933.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___60_2933.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___60_2933.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___60_2933.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___60_2933.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___60_2933.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___60_2933.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___60_2933.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___60_2933.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___60_2933.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___60_2933.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___60_2933.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___60_2933.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___60_2933.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___60_2933.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___60_2933.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___60_2933.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___60_2933.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___60_2933.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___60_2933.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___60_2933.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___60_2933.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___60_2933.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___60_2933.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___60_2933.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___60_2933.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___60_2933.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___60_2933.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let env3 =
                      let uu___61_2935 = env2  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___61_2935.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___61_2935.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___61_2935.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___61_2935.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___61_2935.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___61_2935.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___61_2935.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___61_2935.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___61_2935.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___61_2935.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___61_2935.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___61_2935.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___61_2935.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___61_2935.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___61_2935.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___61_2935.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___61_2935.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___61_2935.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___61_2935.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes = true;
                        FStar_TypeChecker_Env.failhard =
                          (uu___61_2935.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___61_2935.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___61_2935.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___61_2935.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___61_2935.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___61_2935.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___61_2935.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___61_2935.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___61_2935.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___61_2935.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___61_2935.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___61_2935.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___61_2935.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___61_2935.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___61_2935.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___61_2935.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___61_2935.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____2936 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ  in
                    (match uu____2936 with
                     | (ps,w) ->
                         ((let uu____2950 = FStar_ST.op_Bang tacdbg  in
                           if uu____2950
                           then
                             let uu____2970 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____2970
                           else ());
                          (let uu____2972 =
                             FStar_Util.record_time
                               (fun uu____2982  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____2972 with
                           | (res,ms) ->
                               ((let uu____2996 = FStar_ST.op_Bang tacdbg  in
                                 if uu____2996
                                 then
                                   let uu____3016 =
                                     FStar_Syntax_Print.term_to_string
                                       tactic1
                                      in
                                   let uu____3017 =
                                     FStar_Util.string_of_int ms  in
                                   let uu____3018 =
                                     FStar_Syntax_Print.lid_to_string
                                       env3.FStar_TypeChecker_Env.curmodule
                                      in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____3016 uu____3017 uu____3018
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____3026,ps1) ->
                                     ((let uu____3029 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____3029
                                       then
                                         let uu____3049 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____3049
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____3056 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____3056
                                           then
                                             let uu____3057 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____3057
                                              then ()
                                              else
                                                (let uu____3059 =
                                                   let uu____3060 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____3060
                                                    in
                                                 failwith uu____3059))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___62_3063 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___62_3063.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___62_3063.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___62_3063.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____3065 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env3 g1
                                            in
                                         FStar_All.pipe_right uu____3065
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____3072 =
                                         let uu____3073 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____3073 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____3072 "at the time of failure");
                                      (let uu____3074 =
                                         let uu____3079 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____3079)
                                          in
                                       FStar_Errors.raise_error uu____3074
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____3089 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____3093 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____3097 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3146 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3182 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3232 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3270 . 'Auu____3270 -> 'Auu____3270 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3289 = FStar_Syntax_Util.head_and_args t  in
        match uu____3289 with
        | (hd1,args) ->
            let uu____3326 =
              let uu____3339 =
                let uu____3340 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3340.FStar_Syntax_Syntax.n  in
              (uu____3339, args)  in
            (match uu____3326 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3353))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3416 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3416 with
                       | (gs,uu____3424) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3431 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3431 with
                       | (gs,uu____3439) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3490 =
                        let uu____3497 =
                          let uu____3500 =
                            let uu____3501 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3501
                             in
                          [uu____3500]  in
                        (FStar_Syntax_Util.t_true, uu____3497)  in
                      Simplified uu____3490
                  | Both  ->
                      let uu____3512 =
                        let uu____3525 =
                          let uu____3528 =
                            let uu____3529 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3529
                             in
                          [uu____3528]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3525)  in
                      Dual uu____3512
                  | Neg  -> Simplified (assertion, []))
             | uu____3550 -> Unchanged t)
  
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
    fun uu___59_3630  ->
      match uu___59_3630 with
      | Unchanged t -> let uu____3636 = f t  in Unchanged uu____3636
      | Simplified (t,gs) ->
          let uu____3643 = let uu____3650 = f t  in (uu____3650, gs)  in
          Simplified uu____3643
      | Dual (tn,tp,gs) ->
          let uu____3660 =
            let uu____3669 = f tn  in
            let uu____3670 = f tp  in (uu____3669, uu____3670, gs)  in
          Dual uu____3660
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3724 = f t1 t2  in Unchanged uu____3724
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3736 = let uu____3743 = f t1 t2  in (uu____3743, gs)
               in
            Simplified uu____3736
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3757 = let uu____3764 = f t1 t2  in (uu____3764, gs)
               in
            Simplified uu____3757
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3783 =
              let uu____3790 = f t1 t2  in
              (uu____3790, (FStar_List.append gs1 gs2))  in
            Simplified uu____3783
        | uu____3793 ->
            let uu____3802 = explode x  in
            (match uu____3802 with
             | (n1,p1,gs1) ->
                 let uu____3820 = explode y  in
                 (match uu____3820 with
                  | (n2,p2,gs2) ->
                      let uu____3838 =
                        let uu____3847 = f n1 n2  in
                        let uu____3848 = f p1 p2  in
                        (uu____3847, uu____3848, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3838))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3913 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3913
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3956  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3990 =
              let uu____3991 = FStar_Syntax_Subst.compress t  in
              uu____3991.FStar_Syntax_Syntax.n  in
            match uu____3990 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____4003 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____4003 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____4027 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____4027 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4045;
                   FStar_Syntax_Syntax.vars = uu____4046;_},(p,uu____4048)::
                 (q,uu____4050)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____4090 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4090
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____4093 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____4093 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4099 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4099.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4103;
                   FStar_Syntax_Syntax.vars = uu____4104;_},(p,uu____4106)::
                 (q,uu____4108)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4148 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4148
                   in
                let xq =
                  let uu____4150 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4150
                   in
                let r1 =
                  let uu____4152 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4152 p  in
                let r2 =
                  let uu____4154 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4154 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4157,Unchanged uu____4158) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4168 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4168.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4171 ->
                     let uu____4176 = explode r1  in
                     (match uu____4176 with
                      | (pn,pp,gs1) ->
                          let uu____4194 = explode r2  in
                          (match uu____4194 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4215 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4216 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4215
                                   uu____4216
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4268  ->
                       fun r  ->
                         match uu____4268 with
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
                let uu____4386 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4386 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4420  ->
                            match uu____4420 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4434 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___63_4458 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___63_4458.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___63_4458.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4434 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4478 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4478.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4524 = traverse f pol e t1  in
                let uu____4529 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4529 uu____4524
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___64_4567 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___64_4567.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___64_4567.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4574 =
                f pol e
                  (let uu___65_4578 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___65_4578.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___65_4578.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4574
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___66_4588 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___66_4588.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___66_4588.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4589 = explode rp  in
              (match uu____4589 with
               | (uu____4598,p',gs') ->
                   Dual
                     ((let uu___67_4612 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___67_4612.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___67_4612.FStar_Syntax_Syntax.vars)
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
      (let uu____4647 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4647);
      (let uu____4668 = FStar_ST.op_Bang tacdbg  in
       if uu____4668
       then
         let uu____4688 =
           let uu____4689 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4689
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4690 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4688
           uu____4690
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4719 =
         let uu____4726 = traverse by_tactic_interp Pos env goal  in
         match uu____4726 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4744 -> failwith "no"  in
       match uu____4719 with
       | (t',gs) ->
           ((let uu____4766 = FStar_ST.op_Bang tacdbg  in
             if uu____4766
             then
               let uu____4786 =
                 let uu____4787 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4787
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4788 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4786 uu____4788
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4835  ->
                    fun g  ->
                      match uu____4835 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4880 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____4880 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4883 =
                                  let uu____4888 =
                                    let uu____4889 =
                                      FStar_Syntax_Print.term_to_string
                                        g.FStar_Tactics_Types.goal_ty
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____4889
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____4888)
                                   in
                                FStar_Errors.raise_error uu____4883
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4892 = FStar_ST.op_Bang tacdbg  in
                            if uu____4892
                            then
                              let uu____4912 = FStar_Util.string_of_int n1
                                 in
                              let uu____4913 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4912 uu____4913
                            else ());
                           (let gt' =
                              let uu____4916 =
                                let uu____4917 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4917
                                 in
                              FStar_TypeChecker_Util.label uu____4916
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____4932 = s1  in
             match uu____4932 with
             | (uu____4953,gs1) ->
                 let uu____4971 =
                   let uu____4978 = FStar_Options.peek ()  in
                   (env, t', uu____4978)  in
                 uu____4971 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4989 =
        let uu____4990 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4990  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4989 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4991 =
      let uu____4992 =
        let uu____4993 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4994 =
          let uu____4997 = FStar_Syntax_Syntax.as_arg a  in [uu____4997]  in
        uu____4993 :: uu____4994  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4992  in
    uu____4991 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____5010 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____5010);
        (let uu____5030 =
           let uu____5037 = reify_tactic tau  in
           run_tactic_on_typ uu____5037 env typ  in
         match uu____5030 with
         | (gs,w) ->
             let uu____5044 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5048 =
                      let uu____5049 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5049  in
                    Prims.op_Negation uu____5048) gs
                in
             if uu____5044
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
      (let uu____5064 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5064);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____5085 =
         let uu____5092 = reify_tactic tau  in
         run_tactic_on_typ uu____5092 env typ  in
       match uu____5085 with
       | (gs,w) ->
           ((let uu____5102 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5106 =
                      let uu____5107 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5107  in
                    Prims.op_Negation uu____5106) gs
                in
             if uu____5102
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
             let uu____5112 =
               let uu____5117 =
                 FStar_Syntax_Embeddings.e_list
                   FStar_Reflection_Embeddings.e_sigelt
                  in
               FStar_Syntax_Embeddings.unembed uu____5117 w1  in
             FStar_All.pipe_left FStar_Util.must uu____5112)))
  