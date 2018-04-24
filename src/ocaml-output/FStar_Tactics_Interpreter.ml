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
  fun reflect ->
    fun t ->
      fun er ->
        fun nm ->
          fun psc ->
            fun args ->
              match args with
              | (embedded_state, uu____94)::[] ->
                  let uu____111 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Tactics_Embedding.e_proofstate embedded_state in
                  FStar_Util.bind_opt uu____111
                    (fun ps ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                       FStar_Tactics_Basic.log ps1
                         (fun uu____124 ->
                            let uu____125 = FStar_Ident.string_of_lid nm in
                            let uu____126 =
                              FStar_Syntax_Print.args_to_string args in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____125 uu____126);
                       (let res =
                          let uu____128 = FStar_Tactics_Embedding.e_result er in
                          let uu____133 =
                            FStar_TypeChecker_Normalize.psc_range psc in
                          let uu____134 = FStar_Tactics_Basic.run t ps1 in
                          FStar_Syntax_Embeddings.embed uu____128 uu____133
                            uu____134 in
                        FStar_Pervasives_Native.Some res))
              | uu____139 ->
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
  fun reflect ->
    fun t ->
      fun ea ->
        fun er ->
          fun nm ->
            fun psc ->
              fun args ->
                match args with
                | (a, uu____217)::(embedded_state, uu____219)::[] ->
                    let uu____246 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state in
                    FStar_Util.bind_opt uu____246
                      (fun ps ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____259 ->
                              let uu____260 = FStar_Ident.string_of_lid nm in
                              let uu____261 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____260 uu____261);
                         (let uu____262 =
                            FStar_Syntax_Embeddings.unembed ea a in
                          FStar_Util.bind_opt uu____262
                            (fun a1 ->
                               let res =
                                 let uu____272 = t a1 in
                                 FStar_Tactics_Basic.run uu____272 ps1 in
                               let uu____275 =
                                 let uu____276 =
                                   FStar_Tactics_Embedding.e_result er in
                                 let uu____281 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Syntax_Embeddings.embed uu____276
                                   uu____281 res in
                               FStar_Pervasives_Native.Some uu____275)))
                | uu____284 ->
                    let uu____285 =
                      let uu____286 = FStar_Ident.string_of_lid nm in
                      let uu____287 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____286 uu____287 in
                    failwith uu____285
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
  fun reflect ->
    fun t ->
      fun ea ->
        fun er ->
          fun nm ->
            fun psc ->
              fun args ->
                match args with
                | (a, uu____370)::(embedded_state, uu____372)::[] ->
                    let uu____399 =
                      FStar_Syntax_Embeddings.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state in
                    FStar_Util.bind_opt uu____399
                      (fun ps ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____412 ->
                              let uu____413 = FStar_Ident.string_of_lid nm in
                              let uu____414 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____413 uu____414);
                         (let uu____415 =
                            FStar_Syntax_Embeddings.unembed ea a in
                          FStar_Util.bind_opt uu____415
                            (fun a1 ->
                               let res =
                                 let uu____425 = t psc a1 in
                                 FStar_Tactics_Basic.run uu____425 ps1 in
                               let uu____428 =
                                 let uu____429 =
                                   FStar_Tactics_Embedding.e_result er in
                                 let uu____434 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Syntax_Embeddings.embed uu____429
                                   uu____434 res in
                               FStar_Pervasives_Native.Some uu____428)))
                | uu____437 ->
                    let uu____438 =
                      let uu____439 = FStar_Ident.string_of_lid nm in
                      let uu____440 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____439 uu____440 in
                    failwith uu____438
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
  fun reflect ->
    fun t ->
      fun ea ->
        fun eb ->
          fun er ->
            fun nm ->
              fun psc ->
                fun args ->
                  match args with
                  | (a, uu____537)::(b, uu____539)::(embedded_state,
                                                     uu____541)::[]
                      ->
                      let uu____578 =
                        FStar_Syntax_Embeddings.unembed
                          FStar_Tactics_Embedding.e_proofstate embedded_state in
                      FStar_Util.bind_opt uu____578
                        (fun ps ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____591 ->
                                let uu____592 = FStar_Ident.string_of_lid nm in
                                let uu____593 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____592
                                  uu____593);
                           (let uu____594 =
                              FStar_Syntax_Embeddings.unembed ea a in
                            FStar_Util.bind_opt uu____594
                              (fun a1 ->
                                 let uu____600 =
                                   FStar_Syntax_Embeddings.unembed eb b in
                                 FStar_Util.bind_opt uu____600
                                   (fun b1 ->
                                      let res =
                                        let uu____610 = t a1 b1 in
                                        FStar_Tactics_Basic.run uu____610 ps1 in
                                      let uu____613 =
                                        let uu____614 =
                                          FStar_Tactics_Embedding.e_result er in
                                        let uu____619 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc in
                                        FStar_Syntax_Embeddings.embed
                                          uu____614 uu____619 res in
                                      FStar_Pervasives_Native.Some uu____613))))
                  | uu____622 ->
                      let uu____623 =
                        let uu____624 = FStar_Ident.string_of_lid nm in
                        let uu____625 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____624 uu____625 in
                      failwith uu____623
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
  fun reflect ->
    fun t ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun er ->
              fun nm ->
                fun psc ->
                  fun args ->
                    match args with
                    | (a, uu____741)::(b, uu____743)::(c, uu____745)::
                        (embedded_state, uu____747)::[] ->
                        let uu____794 =
                          FStar_Syntax_Embeddings.unembed
                            FStar_Tactics_Embedding.e_proofstate
                            embedded_state in
                        FStar_Util.bind_opt uu____794
                          (fun ps ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____807 ->
                                  let uu____808 =
                                    FStar_Ident.string_of_lid nm in
                                  let uu____809 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____808
                                    uu____809);
                             (let uu____810 =
                                FStar_Syntax_Embeddings.unembed ea a in
                              FStar_Util.bind_opt uu____810
                                (fun a1 ->
                                   let uu____816 =
                                     FStar_Syntax_Embeddings.unembed eb b in
                                   FStar_Util.bind_opt uu____816
                                     (fun b1 ->
                                        let uu____822 =
                                          FStar_Syntax_Embeddings.unembed ec
                                            c in
                                        FStar_Util.bind_opt uu____822
                                          (fun c1 ->
                                             let res =
                                               let uu____832 = t a1 b1 c1 in
                                               FStar_Tactics_Basic.run
                                                 uu____832 ps1 in
                                             let uu____835 =
                                               let uu____836 =
                                                 FStar_Tactics_Embedding.e_result
                                                   er in
                                               let uu____841 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc in
                                               FStar_Syntax_Embeddings.embed
                                                 uu____836 uu____841 res in
                                             FStar_Pervasives_Native.Some
                                               uu____835)))))
                    | uu____844 ->
                        let uu____845 =
                          let uu____846 = FStar_Ident.string_of_lid nm in
                          let uu____847 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____846 uu____847 in
                        failwith uu____845
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
  fun reflect ->
    fun t ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun ed ->
              fun er ->
                fun nm ->
                  fun psc ->
                    fun args ->
                      match args with
                      | (a, uu____982)::(b, uu____984)::(c, uu____986)::
                          (d, uu____988)::(embedded_state, uu____990)::[] ->
                          let uu____1047 =
                            FStar_Syntax_Embeddings.unembed
                              FStar_Tactics_Embedding.e_proofstate
                              embedded_state in
                          FStar_Util.bind_opt uu____1047
                            (fun ps ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps in
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____1060 ->
                                    let uu____1061 =
                                      FStar_Ident.string_of_lid nm in
                                    let uu____1062 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n"
                                      uu____1061 uu____1062);
                               (let uu____1063 =
                                  FStar_Syntax_Embeddings.unembed ea a in
                                FStar_Util.bind_opt uu____1063
                                  (fun a1 ->
                                     let uu____1069 =
                                       FStar_Syntax_Embeddings.unembed eb b in
                                     FStar_Util.bind_opt uu____1069
                                       (fun b1 ->
                                          let uu____1075 =
                                            FStar_Syntax_Embeddings.unembed
                                              ec c in
                                          FStar_Util.bind_opt uu____1075
                                            (fun c1 ->
                                               let uu____1081 =
                                                 FStar_Syntax_Embeddings.unembed
                                                   ed d in
                                               FStar_Util.bind_opt uu____1081
                                                 (fun d1 ->
                                                    let res =
                                                      let uu____1091 =
                                                        t a1 b1 c1 d1 in
                                                      FStar_Tactics_Basic.run
                                                        uu____1091 ps1 in
                                                    let uu____1094 =
                                                      let uu____1095 =
                                                        FStar_Tactics_Embedding.e_result
                                                          er in
                                                      let uu____1100 =
                                                        FStar_TypeChecker_Normalize.psc_range
                                                          psc in
                                                      FStar_Syntax_Embeddings.embed
                                                        uu____1095 uu____1100
                                                        res in
                                                    FStar_Pervasives_Native.Some
                                                      uu____1094))))))
                      | uu____1103 ->
                          let uu____1104 =
                            let uu____1105 = FStar_Ident.string_of_lid nm in
                            let uu____1106 =
                              FStar_Syntax_Print.args_to_string args in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____1105 uu____1106 in
                          failwith uu____1104
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
  fun reflect ->
    fun t ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun ed ->
              fun ee ->
                fun er ->
                  fun nm ->
                    fun psc ->
                      fun args ->
                        match args with
                        | (a, uu____1260)::(b, uu____1262)::(c, uu____1264)::
                            (d, uu____1266)::(e, uu____1268)::(embedded_state,
                                                               uu____1270)::[]
                            ->
                            let uu____1337 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Tactics_Embedding.e_proofstate
                                embedded_state in
                            FStar_Util.bind_opt uu____1337
                              (fun ps ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1350 ->
                                      let uu____1351 =
                                        FStar_Ident.string_of_lid nm in
                                      let uu____1352 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1351 uu____1352);
                                 (let uu____1353 =
                                    FStar_Syntax_Embeddings.unembed ea a in
                                  FStar_Util.bind_opt uu____1353
                                    (fun a1 ->
                                       let uu____1359 =
                                         FStar_Syntax_Embeddings.unembed eb b in
                                       FStar_Util.bind_opt uu____1359
                                         (fun b1 ->
                                            let uu____1365 =
                                              FStar_Syntax_Embeddings.unembed
                                                ec c in
                                            FStar_Util.bind_opt uu____1365
                                              (fun c1 ->
                                                 let uu____1371 =
                                                   FStar_Syntax_Embeddings.unembed
                                                     ed d in
                                                 FStar_Util.bind_opt
                                                   uu____1371
                                                   (fun d1 ->
                                                      let uu____1377 =
                                                        FStar_Syntax_Embeddings.unembed
                                                          ee e in
                                                      FStar_Util.bind_opt
                                                        uu____1377
                                                        (fun e1 ->
                                                           let res =
                                                             let uu____1387 =
                                                               t a1 b1 c1 d1
                                                                 e1 in
                                                             FStar_Tactics_Basic.run
                                                               uu____1387 ps1 in
                                                           let uu____1390 =
                                                             let uu____1391 =
                                                               FStar_Tactics_Embedding.e_result
                                                                 er in
                                                             let uu____1396 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc in
                                                             FStar_Syntax_Embeddings.embed
                                                               uu____1391
                                                               uu____1396 res in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1390)))))))
                        | uu____1399 ->
                            let uu____1400 =
                              let uu____1401 = FStar_Ident.string_of_lid nm in
                              let uu____1402 =
                                FStar_Syntax_Print.args_to_string args in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1401 uu____1402 in
                            failwith uu____1400
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
  fun reflect ->
    fun t ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun ed ->
              fun ee ->
                fun ef ->
                  fun er ->
                    fun nm ->
                      fun psc ->
                        fun args ->
                          match args with
                          | (a, uu____1575)::(b, uu____1577)::(c, uu____1579)::
                              (d, uu____1581)::(e, uu____1583)::(f,
                                                                 uu____1585)::
                              (embedded_state, uu____1587)::[] ->
                              let uu____1664 =
                                FStar_Syntax_Embeddings.unembed
                                  FStar_Tactics_Embedding.e_proofstate
                                  embedded_state in
                              FStar_Util.bind_opt uu____1664
                                (fun ps ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps in
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1677 ->
                                        let uu____1678 =
                                          FStar_Ident.string_of_lid nm in
                                        let uu____1679 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1678 uu____1679);
                                   (let uu____1680 =
                                      FStar_Syntax_Embeddings.unembed ea a in
                                    FStar_Util.bind_opt uu____1680
                                      (fun a1 ->
                                         let uu____1686 =
                                           FStar_Syntax_Embeddings.unembed eb
                                             b in
                                         FStar_Util.bind_opt uu____1686
                                           (fun b1 ->
                                              let uu____1692 =
                                                FStar_Syntax_Embeddings.unembed
                                                  ec c in
                                              FStar_Util.bind_opt uu____1692
                                                (fun c1 ->
                                                   let uu____1698 =
                                                     FStar_Syntax_Embeddings.unembed
                                                       ed d in
                                                   FStar_Util.bind_opt
                                                     uu____1698
                                                     (fun d1 ->
                                                        let uu____1704 =
                                                          FStar_Syntax_Embeddings.unembed
                                                            ee e in
                                                        FStar_Util.bind_opt
                                                          uu____1704
                                                          (fun e1 ->
                                                             let uu____1710 =
                                                               FStar_Syntax_Embeddings.unembed
                                                                 ef f in
                                                             FStar_Util.bind_opt
                                                               uu____1710
                                                               (fun f1 ->
                                                                  let res =
                                                                    let uu____1720
                                                                    =
                                                                    t a1 b1
                                                                    c1 d1 e1
                                                                    f1 in
                                                                    FStar_Tactics_Basic.run
                                                                    uu____1720
                                                                    ps1 in
                                                                  let uu____1723
                                                                    =
                                                                    let uu____1724
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er in
                                                                    let uu____1729
                                                                    =
                                                                    FStar_TypeChecker_Normalize.psc_range
                                                                    psc in
                                                                    FStar_Syntax_Embeddings.embed
                                                                    uu____1724
                                                                    uu____1729
                                                                    res in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____1723))))))))
                          | uu____1732 ->
                              let uu____1733 =
                                let uu____1734 = FStar_Ident.string_of_lid nm in
                                let uu____1735 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1734 uu____1735 in
                              failwith uu____1733
let (step_from_native_step :
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Normalize.primitive_step)
  =
  fun s ->
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
        (fun psc -> fun args -> s.FStar_Tactics_Native.tactic psc args)
    }
let rec e_tactic_0' :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er ->
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____1879 ->
         fun uu____1880 -> failwith "Impossible: embedding tactic (0)?")
      (fun w ->
         fun t ->
           let uu____1888 = unembed_tactic_0 er t in
           FStar_All.pipe_left
             (fun _0_17 -> FStar_Pervasives_Native.Some _0_17) uu____1888)
      FStar_Syntax_Syntax.t_unit
and e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Basic.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea ->
    fun er ->
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____1912 ->
           fun uu____1913 -> failwith "Impossible: embedding tactic (1)?")
        (fun w -> fun t -> unembed_tactic_1 ea er t)
        FStar_Syntax_Syntax.t_unit
and (primitive_steps :
  unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____1922 ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.auto_reflect =
          (FStar_Pervasives_Native.Some (arity - (Prims.parse_int "1")));
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation =
          (fun psc -> fun args -> interpretation nm1 psc args)
      } in
    let native_tactics = FStar_Tactics_Native.list_all () in
    let native_tactics_steps =
      FStar_List.map step_from_native_step native_tactics in
    let mktac1 name f ea er =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 false f ea er) in
    let mktac2 name f ea eb er =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 false f ea eb er) in
    let mktac3 name f ea eb ec er =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 false f ea eb ec er) in
    let mktac5 name f ea eb ec ed ee er =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 false f ea eb ec ed ee er) in
    let decr_depth_interp psc args =
      match args with
      | (ps, uu____2328)::[] ->
          let uu____2345 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps in
          FStar_Util.bind_opt uu____2345
            (fun ps1 ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____2353 =
                 let uu____2354 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____2355 = FStar_Tactics_Types.decr_depth ps2 in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2354 uu____2355 in
               FStar_Pervasives_Native.Some uu____2353)
      | uu____2356 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____2360 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____2360;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp psc args =
      match args with
      | (ps, uu____2377)::[] ->
          let uu____2394 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps in
          FStar_Util.bind_opt uu____2394
            (fun ps1 ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____2402 =
                 let uu____2403 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____2404 = FStar_Tactics_Types.incr_depth ps2 in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2403 uu____2404 in
               FStar_Pervasives_Native.Some uu____2402)
      | uu____2405 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____2409 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____2409;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp psc args =
      match args with
      | (ps, uu____2430)::[] ->
          let uu____2447 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps in
          FStar_Util.bind_opt uu____2447
            (fun ps1 ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2460 -> failwith "Unexpected application of tracepoint" in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps, uu____2481)::(r, uu____2483)::[] ->
          let uu____2510 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps in
          FStar_Util.bind_opt uu____2510
            (fun ps1 ->
               let uu____2516 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_range r in
               FStar_Util.bind_opt uu____2516
                 (fun r1 ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1 in
                    let uu____2524 =
                      let uu____2525 =
                        FStar_TypeChecker_Normalize.psc_range psc in
                      FStar_Syntax_Embeddings.embed
                        FStar_Tactics_Embedding.e_proofstate uu____2525 ps' in
                    FStar_Pervasives_Native.Some uu____2524))
      | uu____2526 ->
          failwith "Unexpected application of set_proofstate_range" in
    let push_binder_interp psc args =
      match args with
      | (env_t, uu____2545)::(b, uu____2547)::[] ->
          let uu____2574 =
            FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_env
              env_t in
          FStar_Util.bind_opt uu____2574
            (fun env ->
               let uu____2580 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Reflection_Embeddings.e_binder b in
               FStar_Util.bind_opt uu____2580
                 (fun b1 ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1] in
                    let uu____2588 =
                      FStar_Syntax_Embeddings.embed
                        FStar_Reflection_Embeddings.e_env
                        env_t.FStar_Syntax_Syntax.pos env1 in
                    FStar_Pervasives_Native.Some uu____2588))
      | uu____2589 -> failwith "Unexpected application of push_binder" in
    let set_proofstate_range_step =
      let nm =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation =
          set_proofstate_range_interp
      } in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      } in
    let push_binder_step =
      let nm =
        FStar_Tactics_Embedding.fstar_tactics_lid'
          ["Builtins"; "push_binder"] in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = push_binder_interp
      } in
    let uu____2598 =
      let uu____2601 =
        mktac2 "fail" (fun uu____2603 -> FStar_Tactics_Basic.fail)
          FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string
          FStar_Syntax_Embeddings.e_any in
      let uu____2604 =
        let uu____2607 =
          mktac1 "trivial" FStar_Tactics_Basic.trivial
            FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit in
        let uu____2608 =
          let uu____2611 =
            let uu____2612 = e_tactic_0' FStar_Syntax_Embeddings.e_any in
            let uu____2617 =
              FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any in
            mktac2 "__trytac" (fun uu____2627 -> FStar_Tactics_Basic.trytac)
              FStar_Syntax_Embeddings.e_any uu____2612 uu____2617 in
          let uu____2628 =
            let uu____2631 =
              mktac1 "intro" FStar_Tactics_Basic.intro
                FStar_Syntax_Embeddings.e_unit
                FStar_Reflection_Embeddings.e_binder in
            let uu____2632 =
              let uu____2635 =
                let uu____2636 =
                  FStar_Syntax_Embeddings.e_tuple2
                    FStar_Reflection_Embeddings.e_binder
                    FStar_Reflection_Embeddings.e_binder in
                mktac1 "intro_rec" FStar_Tactics_Basic.intro_rec
                  FStar_Syntax_Embeddings.e_unit uu____2636 in
              let uu____2647 =
                let uu____2650 =
                  let uu____2651 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Syntax_Embeddings.e_norm_step in
                  mktac1 "norm" FStar_Tactics_Basic.norm uu____2651
                    FStar_Syntax_Embeddings.e_unit in
                let uu____2658 =
                  let uu____2661 =
                    let uu____2662 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_norm_step in
                    mktac3 "norm_term_env" FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Embeddings.e_env uu____2662
                      FStar_Reflection_Embeddings.e_term
                      FStar_Reflection_Embeddings.e_term in
                  let uu____2669 =
                    let uu____2672 =
                      let uu____2673 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step in
                      mktac2 "norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____2673
                        FStar_Reflection_Embeddings.e_binder
                        FStar_Syntax_Embeddings.e_unit in
                    let uu____2680 =
                      let uu____2683 =
                        mktac2 "rename_to" FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_string
                          FStar_Syntax_Embeddings.e_unit in
                      let uu____2684 =
                        let uu____2687 =
                          mktac1 "binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_unit in
                        let uu____2688 =
                          let uu____2691 =
                            mktac1 "revert" FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Syntax_Embeddings.e_unit in
                          let uu____2692 =
                            let uu____2695 =
                              mktac1 "clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit in
                            let uu____2696 =
                              let uu____2699 =
                                mktac1 "clear" FStar_Tactics_Basic.clear
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit in
                              let uu____2700 =
                                let uu____2703 =
                                  mktac1 "rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_unit in
                                let uu____2704 =
                                  let uu____2707 =
                                    mktac1 "smt" FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit in
                                  let uu____2708 =
                                    let uu____2711 =
                                      mktac1 "refine_intro"
                                        FStar_Tactics_Basic.refine_intro
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit in
                                    let uu____2712 =
                                      let uu____2715 =
                                        mktac2 "t_exact"
                                          FStar_Tactics_Basic.t_exact
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Syntax_Embeddings.e_unit in
                                      let uu____2716 =
                                        let uu____2719 =
                                          mktac1 "apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_unit in
                                        let uu____2720 =
                                          let uu____2723 =
                                            mktac1 "apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Embeddings.e_term
                                              FStar_Syntax_Embeddings.e_unit in
                                          let uu____2724 =
                                            let uu____2727 =
                                              mktac1 "apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Syntax_Embeddings.e_unit in
                                            let uu____2728 =
                                              let uu____2731 =
                                                let uu____2732 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any in
                                                let uu____2737 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any in
                                                let uu____2742 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Syntax_Embeddings.e_any
                                                    FStar_Syntax_Embeddings.e_any in
                                                mktac5 "__divide"
                                                  (fun uu____2759 ->
                                                     fun uu____2760 ->
                                                       FStar_Tactics_Basic.divide)
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_int
                                                  uu____2732 uu____2737
                                                  uu____2742 in
                                              let uu____2761 =
                                                let uu____2764 =
                                                  let uu____2765 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit in
                                                  let uu____2770 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit in
                                                  mktac2 "__seq"
                                                    FStar_Tactics_Basic.seq
                                                    uu____2765 uu____2770
                                                    FStar_Syntax_Embeddings.e_unit in
                                                let uu____2779 =
                                                  let uu____2782 =
                                                    mktac1 "set_options"
                                                      FStar_Tactics_Basic.set_options
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Syntax_Embeddings.e_unit in
                                                  let uu____2783 =
                                                    let uu____2786 =
                                                      mktac1 "tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Reflection_Embeddings.e_term in
                                                    let uu____2787 =
                                                      let uu____2790 =
                                                        mktac1 "unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_unit in
                                                      let uu____2791 =
                                                        let uu____2794 =
                                                          mktac2 "unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Reflection_Embeddings.e_term
                                                            FStar_Syntax_Embeddings.e_any in
                                                        let uu____2795 =
                                                          let uu____2798 =
                                                            mktac1 "prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.e_string
                                                              FStar_Syntax_Embeddings.e_unit in
                                                          let uu____2799 =
                                                            let uu____2802 =
                                                              mktac1 "addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit in
                                                            let uu____2803 =
                                                              let uu____2806
                                                                =
                                                                mktac1
                                                                  "print"
                                                                  FStar_Tactics_Basic.print
                                                                  FStar_Syntax_Embeddings.e_string
                                                                  FStar_Syntax_Embeddings.e_unit in
                                                              let uu____2807
                                                                =
                                                                let uu____2810
                                                                  =
                                                                  mktac1
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                let uu____2811
                                                                  =
                                                                  let uu____2814
                                                                    =
                                                                    mktac1
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                  let uu____2815
                                                                    =
                                                                    let uu____2818
                                                                    =
                                                                    mktac1
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2819
                                                                    =
                                                                    let uu____2822
                                                                    =
                                                                    let uu____2823
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____2823
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2830
                                                                    =
                                                                    let uu____2833
                                                                    =
                                                                    let uu____2834
                                                                    =
                                                                    let uu____2846
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____2846 in
                                                                    let uu____2857
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    mktac2
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____2834
                                                                    uu____2857
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2873
                                                                    =
                                                                    let uu____2876
                                                                    =
                                                                    mktac1
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2877
                                                                    =
                                                                    let uu____2880
                                                                    =
                                                                    mktac1
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2881
                                                                    =
                                                                    let uu____2884
                                                                    =
                                                                    mktac1
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2885
                                                                    =
                                                                    let uu____2888
                                                                    =
                                                                    mktac1
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2889
                                                                    =
                                                                    let uu____2892
                                                                    =
                                                                    mktac1
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2893
                                                                    =
                                                                    let uu____2896
                                                                    =
                                                                    mktac1
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2897
                                                                    =
                                                                    let uu____2900
                                                                    =
                                                                    mktac1
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2901
                                                                    =
                                                                    let uu____2904
                                                                    =
                                                                    let uu____2905
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    mktac1
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____2905 in
                                                                    let uu____2916
                                                                    =
                                                                    let uu____2919
                                                                    =
                                                                    mktac1
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env in
                                                                    let uu____2920
                                                                    =
                                                                    let uu____2923
                                                                    =
                                                                    mktac1
                                                                    "cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env in
                                                                    let uu____2924
                                                                    =
                                                                    let uu____2927
                                                                    =
                                                                    mktac1
                                                                    "cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu____2928
                                                                    =
                                                                    let uu____2931
                                                                    =
                                                                    mktac1
                                                                    "cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu____2932
                                                                    =
                                                                    let uu____2935
                                                                    =
                                                                    mktac1
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view in
                                                                    let uu____2936
                                                                    =
                                                                    let uu____2939
                                                                    =
                                                                    mktac1
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu____2940
                                                                    =
                                                                    let uu____2943
                                                                    =
                                                                    mktac1
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    let uu____2944
                                                                    =
                                                                    let uu____2947
                                                                    =
                                                                    mktac1
                                                                    "ngoals"
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    let uu____2948
                                                                    =
                                                                    let uu____2951
                                                                    =
                                                                    mktac1
                                                                    "ngoals_smt"
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    let uu____2952
                                                                    =
                                                                    let uu____2955
                                                                    =
                                                                    mktac1
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool in
                                                                    let uu____2956
                                                                    =
                                                                    let uu____2959
                                                                    =
                                                                    let uu____2960
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    mktac2
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____2960
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu____2967
                                                                    =
                                                                    let uu____2970
                                                                    =
                                                                    mktac2
                                                                    "unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool in
                                                                    let uu____2971
                                                                    =
                                                                    let uu____2974
                                                                    =
                                                                    mktac3
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu____2975
                                                                    =
                                                                    let uu____2978
                                                                    =
                                                                    mktac2
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv in
                                                                    let uu____2979
                                                                    =
                                                                    let uu____2982
                                                                    =
                                                                    mktac1
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____2983
                                                                    =
                                                                    let uu____2986
                                                                    =
                                                                    mktac1
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy in
                                                                    let uu____2987
                                                                    =
                                                                    let uu____2990
                                                                    =
                                                                    mktac1
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    [uu____2990;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step] in
                                                                    uu____2986
                                                                    ::
                                                                    uu____2987 in
                                                                    uu____2982
                                                                    ::
                                                                    uu____2983 in
                                                                    uu____2978
                                                                    ::
                                                                    uu____2979 in
                                                                    uu____2974
                                                                    ::
                                                                    uu____2975 in
                                                                    uu____2970
                                                                    ::
                                                                    uu____2971 in
                                                                    uu____2959
                                                                    ::
                                                                    uu____2967 in
                                                                    uu____2955
                                                                    ::
                                                                    uu____2956 in
                                                                    uu____2951
                                                                    ::
                                                                    uu____2952 in
                                                                    uu____2947
                                                                    ::
                                                                    uu____2948 in
                                                                    uu____2943
                                                                    ::
                                                                    uu____2944 in
                                                                    uu____2939
                                                                    ::
                                                                    uu____2940 in
                                                                    uu____2935
                                                                    ::
                                                                    uu____2936 in
                                                                    uu____2931
                                                                    ::
                                                                    uu____2932 in
                                                                    uu____2927
                                                                    ::
                                                                    uu____2928 in
                                                                    uu____2923
                                                                    ::
                                                                    uu____2924 in
                                                                    uu____2919
                                                                    ::
                                                                    uu____2920 in
                                                                    uu____2904
                                                                    ::
                                                                    uu____2916 in
                                                                    uu____2900
                                                                    ::
                                                                    uu____2901 in
                                                                    uu____2896
                                                                    ::
                                                                    uu____2897 in
                                                                    uu____2892
                                                                    ::
                                                                    uu____2893 in
                                                                    uu____2888
                                                                    ::
                                                                    uu____2889 in
                                                                    uu____2884
                                                                    ::
                                                                    uu____2885 in
                                                                    uu____2880
                                                                    ::
                                                                    uu____2881 in
                                                                    uu____2876
                                                                    ::
                                                                    uu____2877 in
                                                                    uu____2833
                                                                    ::
                                                                    uu____2873 in
                                                                    uu____2822
                                                                    ::
                                                                    uu____2830 in
                                                                    uu____2818
                                                                    ::
                                                                    uu____2819 in
                                                                  uu____2814
                                                                    ::
                                                                    uu____2815 in
                                                                uu____2810 ::
                                                                  uu____2811 in
                                                              uu____2806 ::
                                                                uu____2807 in
                                                            uu____2802 ::
                                                              uu____2803 in
                                                          uu____2798 ::
                                                            uu____2799 in
                                                        uu____2794 ::
                                                          uu____2795 in
                                                      uu____2790 ::
                                                        uu____2791 in
                                                    uu____2786 :: uu____2787 in
                                                  uu____2782 :: uu____2783 in
                                                uu____2764 :: uu____2779 in
                                              uu____2731 :: uu____2761 in
                                            uu____2727 :: uu____2728 in
                                          uu____2723 :: uu____2724 in
                                        uu____2719 :: uu____2720 in
                                      uu____2715 :: uu____2716 in
                                    uu____2711 :: uu____2712 in
                                  uu____2707 :: uu____2708 in
                                uu____2703 :: uu____2704 in
                              uu____2699 :: uu____2700 in
                            uu____2695 :: uu____2696 in
                          uu____2691 :: uu____2692 in
                        uu____2687 :: uu____2688 in
                      uu____2683 :: uu____2684 in
                    uu____2672 :: uu____2680 in
                  uu____2661 :: uu____2669 in
                uu____2650 :: uu____2658 in
              uu____2635 :: uu____2647 in
            uu____2631 :: uu____2632 in
          uu____2611 :: uu____2628 in
        uu____2607 :: uu____2608 in
      uu____2601 :: uu____2604 in
    FStar_List.append uu____2598
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)
and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          ('Aa -> 'Ar FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option
  =
  fun ea ->
    fun er ->
      fun f ->
        FStar_Pervasives_Native.Some
          (fun x ->
             let rng = FStar_Range.dummyRange in
             let x_tm = FStar_Syntax_Embeddings.embed ea rng x in
             let app =
               let uu____3013 =
                 let uu____3018 =
                   let uu____3019 = FStar_Syntax_Syntax.as_arg x_tm in
                   [uu____3019] in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____3018 in
               uu____3013 FStar_Pervasives_Native.None rng in
             unembed_tactic_0 er app)
and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb ->
    fun embedded_tac_b ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state ->
           let rng = embedded_tac_b.FStar_Syntax_Syntax.pos in
           let tm =
             let uu____3042 =
               let uu____3047 =
                 let uu____3048 =
                   let uu____3049 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state in
                   FStar_Syntax_Syntax.as_arg uu____3049 in
                 [uu____3048] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3047 in
             uu____3042 FStar_Pervasives_Native.None rng in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe] in
           (let uu____3056 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose") in
            if uu____3056
            then
              let uu____3057 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____3057
            else ());
           (let result =
              let uu____3060 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____3060 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____3064 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose") in
             if uu____3064
             then
               let uu____3065 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____3065
             else ());
            (let res =
               let uu____3072 = FStar_Tactics_Embedding.e_result eb in
               FStar_Syntax_Embeddings.unembed uu____3072 result in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b, ps)) ->
                 let uu____3085 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____3085
                   (fun uu____3089 -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg, ps)) ->
                 let uu____3094 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____3094
                   (fun uu____3098 -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None ->
                 let uu____3101 =
                   let uu____3106 =
                     let uu____3107 =
                       FStar_Syntax_Print.term_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____3107 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____3106) in
                 FStar_Errors.raise_error uu____3101
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))
and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb ->
    fun embedded_tac_b ->
      let uu____3114 = unembed_tactic_0 eb embedded_tac_b in
      FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some _0_18)
        uu____3114
let (report_implicits :
  FStar_Tactics_Types.proofstate -> FStar_TypeChecker_Env.implicits -> unit)
  =
  fun ps ->
    fun is ->
      let errs =
        FStar_List.map
          (fun uu____3170 ->
             match uu____3170 with
             | (r, uu____3190, uv, uu____3192, ty, rng) ->
                 let uu____3195 =
                   let uu____3196 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____3197 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____3196 uu____3197 r in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____3195, rng)) is in
      match errs with
      | [] -> ()
      | (e, msg, r)::tl1 ->
          (FStar_Tactics_Basic.dump_proofstate ps
             "failing due to uninstantiated implicits";
           FStar_Errors.add_errors tl1;
           FStar_Errors.raise_error (e, msg) r)
let (run_tactic_on_typ :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Tactics_Basic.goal Prims.list, FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun tactic ->
    fun env ->
      fun typ ->
        (let uu____3252 = FStar_ST.op_Bang tacdbg in
         if uu____3252
         then
           let uu____3282 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____3282
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         (let uu____3286 = FStar_ST.op_Bang tacdbg in
          if uu____3286
          then
            let uu____3316 = FStar_Syntax_Print.term_to_string tactic1 in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____3316
          else ());
         (let uu____3318 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1 in
          match uu____3318 with
          | (uu____3331, uu____3332, g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic1 in
                let uu____3339 = FStar_TypeChecker_Env.clear_expected_typ env in
                match uu____3339 with
                | (env1, uu____3353) ->
                    let env2 =
                      let uu___63_3359 = env1 in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___63_3359.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___63_3359.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___63_3359.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___63_3359.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___63_3359.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___63_3359.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___63_3359.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___63_3359.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___63_3359.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___63_3359.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___63_3359.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___63_3359.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___63_3359.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___63_3359.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___63_3359.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___63_3359.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___63_3359.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___63_3359.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___63_3359.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___63_3359.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___63_3359.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___63_3359.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___63_3359.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___63_3359.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___63_3359.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___63_3359.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___63_3359.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___63_3359.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___63_3359.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___63_3359.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___63_3359.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___63_3359.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___63_3359.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___63_3359.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___63_3359.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___63_3359.FStar_TypeChecker_Env.dep_graph)
                      } in
                    let env3 =
                      let uu___64_3361 = env2 in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___64_3361.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___64_3361.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___64_3361.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___64_3361.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___64_3361.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___64_3361.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___64_3361.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___64_3361.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___64_3361.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___64_3361.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___64_3361.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___64_3361.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___64_3361.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___64_3361.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___64_3361.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___64_3361.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___64_3361.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___64_3361.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___64_3361.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes = true;
                        FStar_TypeChecker_Env.failhard =
                          (uu___64_3361.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___64_3361.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___64_3361.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___64_3361.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___64_3361.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___64_3361.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___64_3361.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___64_3361.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___64_3361.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___64_3361.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___64_3361.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___64_3361.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___64_3361.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___64_3361.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___64_3361.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___64_3361.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___64_3361.FStar_TypeChecker_Env.dep_graph)
                      } in
                    let uu____3362 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ in
                    (match uu____3362 with
                     | (ps, w) ->
                         ((let uu____3376 = FStar_ST.op_Bang tacdbg in
                           if uu____3376
                           then
                             let uu____3406 =
                               FStar_Syntax_Print.term_to_string typ in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____3406
                           else ());
                          (let uu____3408 =
                             FStar_Util.record_time
                               (fun uu____3418 ->
                                  FStar_Tactics_Basic.run tau ps) in
                           match uu____3408 with
                           | (res, ms) ->
                               ((let uu____3432 = FStar_ST.op_Bang tacdbg in
                                 if uu____3432
                                 then
                                   let uu____3462 =
                                     FStar_Syntax_Print.term_to_string
                                       tactic1 in
                                   let uu____3463 =
                                     FStar_Util.string_of_int ms in
                                   let uu____3464 =
                                     FStar_Syntax_Print.lid_to_string
                                       env3.FStar_TypeChecker_Env.curmodule in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____3462 uu____3463 uu____3464
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____3472, ps1) ->
                                     ((let uu____3475 =
                                         FStar_ST.op_Bang tacdbg in
                                       if uu____3475
                                       then
                                         let uu____3505 =
                                           FStar_Syntax_Print.term_to_string
                                             w in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____3505
                                       else ());
                                      FStar_List.iter
                                        (fun g1 ->
                                           let uu____3512 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1 in
                                           if uu____3512
                                           then
                                             let uu____3513 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit in
                                             (if uu____3513
                                              then ()
                                              else
                                                (let uu____3515 =
                                                   let uu____3516 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____3516 in
                                                 failwith uu____3515))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___65_3519 =
                                           FStar_TypeChecker_Rel.trivial_guard in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___65_3519.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___65_3519.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___65_3519.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         } in
                                       let g2 =
                                         let uu____3521 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env3 g1 in
                                         FStar_All.pipe_right uu____3521
                                           FStar_TypeChecker_Rel.resolve_implicits_tac in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s, ps1) ->
                                     ((let uu____3528 =
                                         let uu____3529 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____3529 ps1 in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____3528 "at the time of failure");
                                      (let uu____3530 =
                                         let uu____3535 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____3535) in
                                       FStar_Errors.raise_error uu____3530
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee -> match projectee with | Pos -> true | uu____3547 -> false
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee -> match projectee with | Neg -> true | uu____3553 -> false
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee -> match projectee with | Both -> true | uu____3559 -> false
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a, FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a, 'a, FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Unchanged _0 -> true | uu____3614 -> false
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee -> match projectee with | Unchanged _0 -> _0
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Simplified _0 -> true | uu____3654 -> false
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a, FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun projectee -> match projectee with | Simplified _0 -> _0
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Dual _0 -> true | uu____3708 -> false
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a, 'a, FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee -> match projectee with | Dual _0 -> _0
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3749 . 'Auu____3749 -> 'Auu____3749 tres_m =
  fun x -> Unchanged x
let (flip : pol -> pol) =
  fun p -> match p with | Pos -> Neg | Neg -> Pos | Both -> Both
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol ->
    fun e ->
      fun t ->
        let uu____3777 = FStar_Syntax_Util.head_and_args t in
        match uu____3777 with
        | (hd1, args) ->
            let uu____3814 =
              let uu____3827 =
                let uu____3828 = FStar_Syntax_Util.un_uinst hd1 in
                uu____3828.FStar_Syntax_Syntax.n in
              (uu____3827, args) in
            (match uu____3814 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (rett, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____3841))::(tactic,
                                                              FStar_Pervasives_Native.None)::
                (assertion, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos ->
                      let uu____3904 = run_tactic_on_typ tactic e assertion in
                      (match uu____3904 with
                       | (gs, uu____3912) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both ->
                      let uu____3919 = run_tactic_on_typ tactic e assertion in
                      (match uu____3919 with
                       | (gs, uu____3927) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (assertion, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos ->
                      let uu____3978 =
                        let uu____3985 =
                          let uu____3988 =
                            let uu____3989 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3989 in
                          [uu____3988] in
                        (FStar_Syntax_Util.t_true, uu____3985) in
                      Simplified uu____3978
                  | Both ->
                      let uu____4000 =
                        let uu____4013 =
                          let uu____4016 =
                            let uu____4017 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____4017 in
                          [uu____4016] in
                        (assertion, FStar_Syntax_Util.t_true, uu____4013) in
                      Dual uu____4000
                  | Neg -> Simplified (assertion, []))
             | uu____4038 -> Unchanged t)
let explode :
  'a .
    'a tres_m ->
      ('a, 'a, FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun t ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1, gs) -> (t1, t1, gs)
    | Dual (tn, tp, gs) -> (tn, tp, gs)
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f ->
    fun uu___62_4126 ->
      match uu___62_4126 with
      | Unchanged t -> let uu____4132 = f t in Unchanged uu____4132
      | Simplified (t, gs) ->
          let uu____4139 = let uu____4146 = f t in (uu____4146, gs) in
          Simplified uu____4139
      | Dual (tn, tp, gs) ->
          let uu____4156 =
            let uu____4165 = f tn in
            let uu____4166 = f tp in (uu____4165, uu____4166, gs) in
          Dual uu____4156
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f ->
    fun x ->
      fun y ->
        match (x, y) with
        | (Unchanged t1, Unchanged t2) ->
            let uu____4229 = f t1 t2 in Unchanged uu____4229
        | (Unchanged t1, Simplified (t2, gs)) ->
            let uu____4241 = let uu____4248 = f t1 t2 in (uu____4248, gs) in
            Simplified uu____4241
        | (Simplified (t1, gs), Unchanged t2) ->
            let uu____4262 = let uu____4269 = f t1 t2 in (uu____4269, gs) in
            Simplified uu____4262
        | (Simplified (t1, gs1), Simplified (t2, gs2)) ->
            let uu____4288 =
              let uu____4295 = f t1 t2 in
              (uu____4295, (FStar_List.append gs1 gs2)) in
            Simplified uu____4288
        | uu____4298 ->
            let uu____4307 = explode x in
            (match uu____4307 with
             | (n1, p1, gs1) ->
                 let uu____4325 = explode y in
                 (match uu____4325 with
                  | (n2, p2, gs2) ->
                      let uu____4343 =
                        let uu____4352 = f n1 n2 in
                        let uu____4353 = f p1 p2 in
                        (uu____4352, uu____4353, (FStar_List.append gs1 gs2)) in
                      Dual uu____4343))
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____4425 = comb2 (fun l -> fun r -> l :: r) hd1 acc in
          aux tl1 uu____4425 in
    aux (FStar_List.rev rs) (tpure [])
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs ->
    fun m -> comb2 (fun uu____4473 -> fun x -> x) (Simplified ((), gs)) m
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f ->
    fun pol ->
      fun e ->
        fun t ->
          let r =
            let uu____4515 =
              let uu____4516 = FStar_Syntax_Subst.compress t in
              uu____4516.FStar_Syntax_Syntax.n in
            match uu____4515 with
            | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
                let tr = traverse f pol e t1 in
                let uu____4528 =
                  comb1 (fun t' -> FStar_Syntax_Syntax.Tm_uinst (t', us)) in
                uu____4528 tr
            | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
                let tr = traverse f pol e t1 in
                let uu____4554 =
                  comb1 (fun t' -> FStar_Syntax_Syntax.Tm_meta (t', m)) in
                uu____4554 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4574;
                   FStar_Syntax_Syntax.vars = uu____4575;_},
                 (p, uu____4577)::(q, uu____4579)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____4619 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4619 in
                let r1 = traverse f (flip pol) e p in
                let r2 =
                  let uu____4622 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f pol uu____4622 q in
                comb2
                  (fun l ->
                     fun r ->
                       let uu____4628 = FStar_Syntax_Util.mk_imp l r in
                       uu____4628.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4632;
                   FStar_Syntax_Syntax.vars = uu____4633;_},
                 (p, uu____4635)::(q, uu____4637)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4677 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4677 in
                let xq =
                  let uu____4679 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4679 in
                let r1 =
                  let uu____4681 = FStar_TypeChecker_Env.push_bv e xq in
                  traverse f Both uu____4681 p in
                let r2 =
                  let uu____4683 = FStar_TypeChecker_Env.push_bv e xp in
                  traverse f Both uu____4683 q in
                (match (r1, r2) with
                 | (Unchanged uu____4686, Unchanged uu____4687) ->
                     comb2
                       (fun l ->
                          fun r ->
                            let uu____4697 = FStar_Syntax_Util.mk_iff l r in
                            uu____4697.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4700 ->
                     let uu____4705 = explode r1 in
                     (match uu____4705 with
                      | (pn, pp, gs1) ->
                          let uu____4723 = explode r2 in
                          (match uu____4723 with
                           | (qn, qp, gs2) ->
                               let t1 =
                                 let uu____4744 =
                                   FStar_Syntax_Util.mk_imp pn qp in
                                 let uu____4745 =
                                   FStar_Syntax_Util.mk_imp qn pp in
                                 FStar_Syntax_Util.mk_conj uu____4744
                                   uu____4745 in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
                let r0 = traverse f pol e hd1 in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4797 ->
                       fun r ->
                         match uu____4797 with
                         | (a, q) ->
                             let r' = traverse f pol e a in
                             comb2 (fun a1 -> fun args1 -> (a1, q) :: args1)
                               r' r) args (tpure []) in
                comb2
                  (fun hd2 ->
                     fun args1 -> FStar_Syntax_Syntax.Tm_app (hd2, args1)) r0
                  r1
            | FStar_Syntax_Syntax.Tm_abs (bs, t1, k) ->
                let uu____4915 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____4915 with
                 | (bs1, topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let r0 =
                       FStar_List.map
                         (fun uu____4949 ->
                            match uu____4949 with
                            | (bv, aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort in
                                let uu____4963 =
                                  comb1
                                    (fun s' ->
                                       ((let uu___66_4989 = bv in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___66_4989.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___66_4989.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq)) in
                                uu____4963 r) bs1 in
                     let rbs = comb_list r0 in
                     let rt = traverse f pol e' topen in
                     comb2
                       (fun bs2 ->
                          fun t2 ->
                            let uu____5009 = FStar_Syntax_Util.abs bs2 t2 k in
                            uu____5009.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, ef) ->
                let uu____5055 = traverse f pol e t1 in
                let uu____5060 =
                  comb1
                    (fun t2 -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef)) in
                uu____5060 uu____5055
            | x -> tpure x in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___67_5100 = t in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___67_5100.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___67_5100.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn', gs) ->
              let uu____5107 =
                f pol e
                  (let uu___68_5111 = t in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___68_5111.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___68_5111.FStar_Syntax_Syntax.vars)
                   }) in
              emit gs uu____5107
          | Dual (tn, tp, gs) ->
              let rp =
                f pol e
                  (let uu___69_5121 = t in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___69_5121.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___69_5121.FStar_Syntax_Syntax.vars)
                   }) in
              let uu____5122 = explode rp in
              (match uu____5122 with
               | (uu____5131, p', gs') ->
                   Dual
                     ((let uu___70_5145 = t in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___70_5145.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___70_5145.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    fun t ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t in
      FStar_Syntax_Util.un_squash tn
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env, FStar_Syntax_Syntax.term,
        FStar_Options.optionstate) FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun env ->
    fun goal ->
      (let uu____5188 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____5188);
      (let uu____5219 = FStar_ST.op_Bang tacdbg in
       if uu____5219
       then
         let uu____5249 =
           let uu____5250 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____5250
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____5251 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____5249
           uu____5251
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____5280 =
         let uu____5287 = traverse by_tactic_interp Pos env goal in
         match uu____5287 with
         | Unchanged t' -> (t', [])
         | Simplified (t', gs) -> (t', gs)
         | uu____5305 -> failwith "no" in
       match uu____5280 with
       | (t', gs) ->
           ((let uu____5327 = FStar_ST.op_Bang tacdbg in
             if uu____5327
             then
               let uu____5357 =
                 let uu____5358 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____5358
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____5359 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____5357 uu____5359
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5406 ->
                    fun g ->
                      match uu____5406 with
                      | (n1, gs1) ->
                          let phi =
                            let uu____5451 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____5451 with
                            | FStar_Pervasives_Native.None ->
                                let uu____5454 =
                                  let uu____5459 =
                                    let uu____5460 =
                                      FStar_Syntax_Print.term_to_string
                                        g.FStar_Tactics_Types.goal_ty in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5460 in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5459) in
                                FStar_Errors.raise_error uu____5454
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____5463 = FStar_ST.op_Bang tacdbg in
                            if uu____5463
                            then
                              let uu____5493 = FStar_Util.string_of_int n1 in
                              let uu____5494 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5493 uu____5494
                            else ());
                           (let gt' =
                              let uu____5497 =
                                let uu____5498 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____5498 in
                              FStar_TypeChecker_Util.label uu____5497
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____5513 = s1 in
             match uu____5513 with
             | (uu____5534, gs1) ->
                 let uu____5552 =
                   let uu____5559 = FStar_Options.peek () in
                   (env, t', uu____5559) in
                 uu____5552 :: gs1)))
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a ->
    let r =
      let uu____5572 =
        let uu____5573 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____5573 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____5572 [FStar_Syntax_Syntax.U_zero] in
    let uu____5574 =
      let uu____5579 =
        let uu____5580 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____5581 =
          let uu____5584 = FStar_Syntax_Syntax.as_arg a in [uu____5584] in
        uu____5580 :: uu____5581 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____5579 in
    uu____5574 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun typ ->
      fun tau ->
        (let uu____5603 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____5603);
        (let uu____5633 =
           let uu____5640 = reify_tactic tau in
           run_tactic_on_typ uu____5640 env typ in
         match uu____5633 with
         | (gs, w) ->
             let uu____5647 =
               FStar_List.existsML
                 (fun g ->
                    let uu____5651 =
                      let uu____5652 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____5652 in
                    Prims.op_Negation uu____5651) gs in
             if uu____5647
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "synthesis left open goals") typ.FStar_Syntax_Syntax.pos
             else w)
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env ->
    fun tau ->
      (let uu____5671 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____5671);
      (let typ = FStar_Syntax_Syntax.t_decls in
       let uu____5702 =
         let uu____5709 = reify_tactic tau in
         run_tactic_on_typ uu____5709 env typ in
       match uu____5702 with
       | (gs, w) ->
           ((let uu____5719 =
               FStar_List.existsML
                 (fun g ->
                    let uu____5723 =
                      let uu____5724 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____5724 in
                    Prims.op_Negation uu____5723) gs in
             if uu____5719
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
                 FStar_TypeChecker_Normalize.Unmeta] env w in
             let uu____5729 =
               let uu____5734 =
                 FStar_Syntax_Embeddings.e_list
                   FStar_Reflection_Embeddings.e_sigelt in
               FStar_Syntax_Embeddings.unembed uu____5734 w1 in
             FStar_All.pipe_left FStar_Util.must uu____5729)))