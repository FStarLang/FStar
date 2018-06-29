open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mk_tactic_interpretation_0 :
  'r .
    Prims.bool ->
      'r FStar_Tactics_Basic.tac ->
        'r FStar_Syntax_Embeddings.embedding ->
          FStar_Ident.lid ->
            FStar_TypeChecker_Normalize.psc ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun er  ->
        fun nm  ->
          fun psc  ->
            fun ncb  ->
              fun args  ->
                match args with
                | (embedded_state,uu____81)::[] ->
                    let uu____106 =
                      FStar_Reflection_Interpreter.unembed
                        FStar_Tactics_Embedding.e_proofstate embedded_state
                        ncb
                       in
                    FStar_Util.bind_opt uu____106
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____121  ->
                              let uu____122 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____123 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.print2 "Reached %s, args are: %s\n"
                                uu____122 uu____123);
                         (let res =
                            let uu____125 =
                              FStar_Tactics_Embedding.e_result er  in
                            let uu____130 =
                              FStar_TypeChecker_Normalize.psc_range psc  in
                            let uu____131 =
                              FStar_Tactics_Basic.run_safe t ps1  in
                            FStar_Reflection_Interpreter.embed uu____125
                              uu____130 uu____131 ncb
                             in
                          FStar_Pervasives_Native.Some res))
                | uu____138 ->
                    failwith "Unexpected application of tactic primitive"
  
let mk_tactic_interpretation_1 :
  'a 'r .
    Prims.bool ->
      ('a -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Embeddings.norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun er  ->
          fun nm  ->
            fun psc  ->
              fun ncb  ->
                fun args  ->
                  match args with
                  | (a,uu____227)::(embedded_state,uu____229)::[] ->
                      let uu____270 =
                        FStar_Reflection_Interpreter.unembed
                          FStar_Tactics_Embedding.e_proofstate embedded_state
                          ncb
                         in
                      FStar_Util.bind_opt uu____270
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____285  ->
                                let uu____286 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____287 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____286
                                  uu____287);
                           (let uu____288 =
                              FStar_Reflection_Interpreter.unembed ea a ncb
                               in
                            FStar_Util.bind_opt uu____288
                              (fun a1  ->
                                 let res =
                                   let uu____300 = t a1  in
                                   FStar_Tactics_Basic.run_safe uu____300 ps1
                                    in
                                 let uu____303 =
                                   let uu____304 =
                                     FStar_Tactics_Embedding.e_result er  in
                                   let uu____309 =
                                     FStar_TypeChecker_Normalize.psc_range
                                       psc
                                      in
                                   FStar_Reflection_Interpreter.embed
                                     uu____304 uu____309 res ncb
                                    in
                                 FStar_Pervasives_Native.Some uu____303)))
                  | uu____314 ->
                      let uu____315 =
                        let uu____316 = FStar_Ident.string_of_lid nm  in
                        let uu____317 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____316 uu____317
                         in
                      failwith uu____315
  
let mk_tactic_interpretation_1_env :
  'a 'r .
    Prims.bool ->
      (FStar_TypeChecker_Normalize.psc -> 'a -> 'r FStar_Tactics_Basic.tac)
        ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Embeddings.norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun er  ->
          fun nm  ->
            fun psc  ->
              fun ncb  ->
                fun args  ->
                  match args with
                  | (a,uu____411)::(embedded_state,uu____413)::[] ->
                      let uu____454 =
                        FStar_Reflection_Interpreter.unembed
                          FStar_Tactics_Embedding.e_proofstate embedded_state
                          ncb
                         in
                      FStar_Util.bind_opt uu____454
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____469  ->
                                let uu____470 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____471 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____470
                                  uu____471);
                           (let uu____472 =
                              FStar_Reflection_Interpreter.unembed ea a ncb
                               in
                            FStar_Util.bind_opt uu____472
                              (fun a1  ->
                                 let res =
                                   let uu____484 = t psc a1  in
                                   FStar_Tactics_Basic.run_safe uu____484 ps1
                                    in
                                 let uu____487 =
                                   let uu____488 =
                                     FStar_Tactics_Embedding.e_result er  in
                                   let uu____493 =
                                     FStar_TypeChecker_Normalize.psc_range
                                       psc
                                      in
                                   FStar_Reflection_Interpreter.embed
                                     uu____488 uu____493 res ncb
                                    in
                                 FStar_Pervasives_Native.Some uu____487)))
                  | uu____498 ->
                      let uu____499 =
                        let uu____500 = FStar_Ident.string_of_lid nm  in
                        let uu____501 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____500 uu____501
                         in
                      failwith uu____499
  
let mk_tactic_interpretation_2 :
  'a 'b 'r .
    Prims.bool ->
      ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Embeddings.norm_cb ->
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
                fun ncb  ->
                  fun args  ->
                    match args with
                    | (a,uu____609)::(b,uu____611)::(embedded_state,uu____613)::[]
                        ->
                        let uu____670 =
                          FStar_Reflection_Interpreter.unembed
                            FStar_Tactics_Embedding.e_proofstate
                            embedded_state ncb
                           in
                        FStar_Util.bind_opt uu____670
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____685  ->
                                  let uu____686 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____687 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____686
                                    uu____687);
                             (let uu____688 =
                                FStar_Reflection_Interpreter.unembed ea a ncb
                                 in
                              FStar_Util.bind_opt uu____688
                                (fun a1  ->
                                   let uu____696 =
                                     FStar_Reflection_Interpreter.unembed eb
                                       b ncb
                                      in
                                   FStar_Util.bind_opt uu____696
                                     (fun b1  ->
                                        let res =
                                          let uu____708 = t a1 b1  in
                                          FStar_Tactics_Basic.run_safe
                                            uu____708 ps1
                                           in
                                        let uu____711 =
                                          let uu____712 =
                                            FStar_Tactics_Embedding.e_result
                                              er
                                             in
                                          let uu____717 =
                                            FStar_TypeChecker_Normalize.psc_range
                                              psc
                                             in
                                          FStar_Reflection_Interpreter.embed
                                            uu____712 uu____717 res ncb
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____711))))
                    | uu____722 ->
                        let uu____723 =
                          let uu____724 = FStar_Ident.string_of_lid nm  in
                          let uu____725 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____724 uu____725
                           in
                        failwith uu____723
  
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
                    FStar_Syntax_Embeddings.norm_cb ->
                      FStar_Syntax_Syntax.args ->
                        FStar_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun er  ->
              fun nm  ->
                fun psc  ->
                  fun ncb  ->
                    fun args  ->
                      match args with
                      | (a,uu____852)::(b,uu____854)::(c,uu____856)::
                          (embedded_state,uu____858)::[] ->
                          let uu____931 =
                            FStar_Reflection_Interpreter.unembed
                              FStar_Tactics_Embedding.e_proofstate
                              embedded_state ncb
                             in
                          FStar_Util.bind_opt uu____931
                            (fun ps  ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____946  ->
                                    let uu____947 =
                                      FStar_Ident.string_of_lid nm  in
                                    let uu____948 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state
                                       in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n" uu____947
                                      uu____948);
                               (let uu____949 =
                                  FStar_Reflection_Interpreter.unembed ea a
                                    ncb
                                   in
                                FStar_Util.bind_opt uu____949
                                  (fun a1  ->
                                     let uu____957 =
                                       FStar_Reflection_Interpreter.unembed
                                         eb b ncb
                                        in
                                     FStar_Util.bind_opt uu____957
                                       (fun b1  ->
                                          let uu____965 =
                                            FStar_Reflection_Interpreter.unembed
                                              ec c ncb
                                             in
                                          FStar_Util.bind_opt uu____965
                                            (fun c1  ->
                                               let res =
                                                 let uu____977 = t a1 b1 c1
                                                    in
                                                 FStar_Tactics_Basic.run_safe
                                                   uu____977 ps1
                                                  in
                                               let uu____980 =
                                                 let uu____981 =
                                                   FStar_Tactics_Embedding.e_result
                                                     er
                                                    in
                                                 let uu____986 =
                                                   FStar_TypeChecker_Normalize.psc_range
                                                     psc
                                                    in
                                                 FStar_Reflection_Interpreter.embed
                                                   uu____981 uu____986 res
                                                   ncb
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____980)))))
                      | uu____991 ->
                          let uu____992 =
                            let uu____993 = FStar_Ident.string_of_lid nm  in
                            let uu____994 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____993 uu____994
                             in
                          failwith uu____992
  
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
                      FStar_Syntax_Embeddings.norm_cb ->
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
                    fun ncb  ->
                      fun args  ->
                        match args with
                        | (a,uu____1140)::(b,uu____1142)::(c,uu____1144)::
                            (d,uu____1146)::(embedded_state,uu____1148)::[]
                            ->
                            let uu____1237 =
                              FStar_Reflection_Interpreter.unembed
                                FStar_Tactics_Embedding.e_proofstate
                                embedded_state ncb
                               in
                            FStar_Util.bind_opt uu____1237
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1252  ->
                                      let uu____1253 =
                                        FStar_Ident.string_of_lid nm  in
                                      let uu____1254 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state
                                         in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1253 uu____1254);
                                 (let uu____1255 =
                                    FStar_Reflection_Interpreter.unembed ea a
                                      ncb
                                     in
                                  FStar_Util.bind_opt uu____1255
                                    (fun a1  ->
                                       let uu____1263 =
                                         FStar_Reflection_Interpreter.unembed
                                           eb b ncb
                                          in
                                       FStar_Util.bind_opt uu____1263
                                         (fun b1  ->
                                            let uu____1271 =
                                              FStar_Reflection_Interpreter.unembed
                                                ec c ncb
                                               in
                                            FStar_Util.bind_opt uu____1271
                                              (fun c1  ->
                                                 let uu____1279 =
                                                   FStar_Reflection_Interpreter.unembed
                                                     ed d ncb
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____1279
                                                   (fun d1  ->
                                                      let res =
                                                        let uu____1291 =
                                                          t a1 b1 c1 d1  in
                                                        FStar_Tactics_Basic.run_safe
                                                          uu____1291 ps1
                                                         in
                                                      let uu____1294 =
                                                        let uu____1295 =
                                                          FStar_Tactics_Embedding.e_result
                                                            er
                                                           in
                                                        let uu____1300 =
                                                          FStar_TypeChecker_Normalize.psc_range
                                                            psc
                                                           in
                                                        FStar_Reflection_Interpreter.embed
                                                          uu____1295
                                                          uu____1300 res ncb
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____1294))))))
                        | uu____1305 ->
                            let uu____1306 =
                              let uu____1307 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____1308 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1307 uu____1308
                               in
                            failwith uu____1306
  
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
                        FStar_Syntax_Embeddings.norm_cb ->
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
                      fun ncb  ->
                        fun args  ->
                          match args with
                          | (a,uu____1473)::(b,uu____1475)::(c,uu____1477)::
                              (d,uu____1479)::(e,uu____1481)::(embedded_state,uu____1483)::[]
                              ->
                              let uu____1588 =
                                FStar_Reflection_Interpreter.unembed
                                  FStar_Tactics_Embedding.e_proofstate
                                  embedded_state ncb
                                 in
                              FStar_Util.bind_opt uu____1588
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1603  ->
                                        let uu____1604 =
                                          FStar_Ident.string_of_lid nm  in
                                        let uu____1605 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state
                                           in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1604 uu____1605);
                                   (let uu____1606 =
                                      FStar_Reflection_Interpreter.unembed ea
                                        a ncb
                                       in
                                    FStar_Util.bind_opt uu____1606
                                      (fun a1  ->
                                         let uu____1614 =
                                           FStar_Reflection_Interpreter.unembed
                                             eb b ncb
                                            in
                                         FStar_Util.bind_opt uu____1614
                                           (fun b1  ->
                                              let uu____1622 =
                                                FStar_Reflection_Interpreter.unembed
                                                  ec c ncb
                                                 in
                                              FStar_Util.bind_opt uu____1622
                                                (fun c1  ->
                                                   let uu____1630 =
                                                     FStar_Reflection_Interpreter.unembed
                                                       ed d ncb
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____1630
                                                     (fun d1  ->
                                                        let uu____1638 =
                                                          FStar_Reflection_Interpreter.unembed
                                                            ee e ncb
                                                           in
                                                        FStar_Util.bind_opt
                                                          uu____1638
                                                          (fun e1  ->
                                                             let res =
                                                               let uu____1650
                                                                 =
                                                                 t a1 b1 c1
                                                                   d1 e1
                                                                  in
                                                               FStar_Tactics_Basic.run_safe
                                                                 uu____1650
                                                                 ps1
                                                                in
                                                             let uu____1653 =
                                                               let uu____1654
                                                                 =
                                                                 FStar_Tactics_Embedding.e_result
                                                                   er
                                                                  in
                                                               let uu____1659
                                                                 =
                                                                 FStar_TypeChecker_Normalize.psc_range
                                                                   psc
                                                                  in
                                                               FStar_Reflection_Interpreter.embed
                                                                 uu____1654
                                                                 uu____1659
                                                                 res ncb
                                                                in
                                                             FStar_Pervasives_Native.Some
                                                               uu____1653)))))))
                          | uu____1664 ->
                              let uu____1665 =
                                let uu____1666 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____1667 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1666 uu____1667
                                 in
                              failwith uu____1665
  
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
                          FStar_Syntax_Embeddings.norm_cb ->
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
                        fun ncb  ->
                          fun args  ->
                            match args with
                            | (a,uu____1851)::(b,uu____1853)::(c,uu____1855)::
                                (d,uu____1857)::(e,uu____1859)::(f,uu____1861)::
                                (embedded_state,uu____1863)::[] ->
                                let uu____1984 =
                                  FStar_Reflection_Interpreter.unembed
                                    FStar_Tactics_Embedding.e_proofstate
                                    embedded_state ncb
                                   in
                                FStar_Util.bind_opt uu____1984
                                  (fun ps  ->
                                     let ps1 =
                                       FStar_Tactics_Types.set_ps_psc psc ps
                                        in
                                     FStar_Tactics_Basic.log ps1
                                       (fun uu____1999  ->
                                          let uu____2000 =
                                            FStar_Ident.string_of_lid nm  in
                                          let uu____2001 =
                                            FStar_Syntax_Print.term_to_string
                                              embedded_state
                                             in
                                          FStar_Util.print2
                                            "Reached %s, goals are: %s\n"
                                            uu____2000 uu____2001);
                                     (let uu____2002 =
                                        FStar_Reflection_Interpreter.unembed
                                          ea a ncb
                                         in
                                      FStar_Util.bind_opt uu____2002
                                        (fun a1  ->
                                           let uu____2010 =
                                             FStar_Reflection_Interpreter.unembed
                                               eb b ncb
                                              in
                                           FStar_Util.bind_opt uu____2010
                                             (fun b1  ->
                                                let uu____2018 =
                                                  FStar_Reflection_Interpreter.unembed
                                                    ec c ncb
                                                   in
                                                FStar_Util.bind_opt
                                                  uu____2018
                                                  (fun c1  ->
                                                     let uu____2026 =
                                                       FStar_Reflection_Interpreter.unembed
                                                         ed d ncb
                                                        in
                                                     FStar_Util.bind_opt
                                                       uu____2026
                                                       (fun d1  ->
                                                          let uu____2034 =
                                                            FStar_Reflection_Interpreter.unembed
                                                              ee e ncb
                                                             in
                                                          FStar_Util.bind_opt
                                                            uu____2034
                                                            (fun e1  ->
                                                               let uu____2042
                                                                 =
                                                                 FStar_Reflection_Interpreter.unembed
                                                                   ef f ncb
                                                                  in
                                                               FStar_Util.bind_opt
                                                                 uu____2042
                                                                 (fun f1  ->
                                                                    let res =
                                                                    let uu____2054
                                                                    =
                                                                    t a1 b1
                                                                    c1 d1 e1
                                                                    f1  in
                                                                    FStar_Tactics_Basic.run_safe
                                                                    uu____2054
                                                                    ps1  in
                                                                    let uu____2057
                                                                    =
                                                                    let uu____2058
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                    let uu____2063
                                                                    =
                                                                    FStar_TypeChecker_Normalize.psc_range
                                                                    psc  in
                                                                    FStar_Reflection_Interpreter.embed
                                                                    uu____2058
                                                                    uu____2063
                                                                    res ncb
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____2057))))))))
                            | uu____2068 ->
                                let uu____2069 =
                                  let uu____2070 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____2071 =
                                    FStar_Syntax_Print.args_to_string args
                                     in
                                  FStar_Util.format2
                                    "Unexpected application of tactic primitive %s %s"
                                    uu____2070 uu____2071
                                   in
                                failwith uu____2069
  
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
        (fun psc  ->
           fun ncb  ->
             fun args  -> s.FStar_Tactics_Native.tactic psc ncb args)
    }
  
let mk_emb :
  'a .
    (FStar_Range.range ->
       'a -> FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term)
      ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           FStar_Syntax_Embeddings.norm_cb ->
             'a FStar_Pervasives_Native.option)
        -> FStar_Syntax_Syntax.term -> 'a FStar_Syntax_Embeddings.embedding
  =
  fun em  ->
    fun un  ->
      fun t  ->
        let uu____2157 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun norm1  -> em r x norm1)
          (fun x  -> fun w  -> fun norm1  -> un w x norm1) uu____2157
  
let rec e_tactic_0' :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    mk_emb
      (fun uu____2356  ->
         fun uu____2357  ->
           fun uu____2358  -> failwith "Impossible: embedding tactic (0)?")
      (fun _w  ->
         fun t  ->
           fun norm1  ->
             let uu____2372 = unembed_tactic_0 er t norm1  in
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____2372)
      FStar_Syntax_Syntax.t_unit

and e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Basic.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      mk_emb
        (fun uu____2399  ->
           fun uu____2400  ->
             fun uu____2401  -> failwith "Impossible: embedding tactic (1)?")
        (fun w  -> fun t  -> unembed_tactic_1 ea er t)
        FStar_Syntax_Syntax.t_unit

and (primitive_steps :
  unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____2412  ->
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
          (fun psc  ->
             fun norm_cb  -> fun args  -> interpretation nm1 psc norm_cb args)
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
    let decr_depth_interp psc ncb args =
      match args with
      | (ps,uu____2842)::[] ->
          let uu____2867 =
            FStar_Reflection_Interpreter.unembed
              FStar_Tactics_Embedding.e_proofstate ps ncb
             in
          FStar_Util.bind_opt uu____2867
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2877 =
                 let uu____2878 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2879 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Reflection_Interpreter.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2878 uu____2879
                   ncb
                  in
               FStar_Pervasives_Native.Some uu____2877)
      | uu____2882 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____2886 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2886;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc ncb args =
      match args with
      | (ps,uu____2912)::[] ->
          let uu____2937 =
            FStar_Reflection_Interpreter.unembed
              FStar_Tactics_Embedding.e_proofstate ps ncb
             in
          FStar_Util.bind_opt uu____2937
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2947 =
                 let uu____2948 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2949 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Reflection_Interpreter.embed
                   FStar_Tactics_Embedding.e_proofstate uu____2948 uu____2949
                   ncb
                  in
               FStar_Pervasives_Native.Some uu____2947)
      | uu____2952 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____2956 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2956;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc ncb args =
      match args with
      | (ps,uu____2982)::[] ->
          let uu____3007 =
            FStar_Reflection_Interpreter.unembed
              FStar_Tactics_Embedding.e_proofstate ps ncb
             in
          FStar_Util.bind_opt uu____3007
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____3018 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc ncb args =
      match args with
      | (ps,uu____3046)::(r,uu____3048)::[] ->
          let uu____3089 =
            FStar_Reflection_Interpreter.unembed
              FStar_Tactics_Embedding.e_proofstate ps ncb
             in
          FStar_Util.bind_opt uu____3089
            (fun ps1  ->
               let uu____3097 =
                 FStar_Reflection_Interpreter.unembed
                   FStar_Syntax_Embeddings.e_range r ncb
                  in
               FStar_Util.bind_opt uu____3097
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____3107 =
                      let uu____3108 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Reflection_Interpreter.embed
                        FStar_Tactics_Embedding.e_proofstate uu____3108 ps'
                        ncb
                       in
                    FStar_Pervasives_Native.Some uu____3107))
      | uu____3111 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc ncb args =
      match args with
      | (env_t,uu____3139)::(b,uu____3141)::[] ->
          let uu____3182 =
            FStar_Reflection_Interpreter.unembed
              FStar_Reflection_Embeddings.e_env env_t ncb
             in
          FStar_Util.bind_opt uu____3182
            (fun env  ->
               let uu____3190 =
                 FStar_Reflection_Interpreter.unembed
                   FStar_Reflection_Embeddings.e_binder b ncb
                  in
               FStar_Util.bind_opt uu____3190
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____3212 =
                      FStar_Reflection_Interpreter.embed
                        FStar_Reflection_Embeddings.e_env
                        env_t.FStar_Syntax_Syntax.pos env1 ncb
                       in
                    FStar_Pervasives_Native.Some uu____3212))
      | uu____3215 -> failwith "Unexpected application of push_binder"  in
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
    let uu____3224 =
      let uu____3227 =
        mktac2 "fail" (fun uu____3229  -> FStar_Tactics_Basic.fail)
          FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string
          FStar_Syntax_Embeddings.e_any
         in
      let uu____3230 =
        let uu____3233 =
          mktac1 "trivial" FStar_Tactics_Basic.trivial
            FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
           in
        let uu____3234 =
          let uu____3237 =
            let uu____3238 = e_tactic_0' FStar_Syntax_Embeddings.e_any  in
            let uu____3243 =
              FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any
               in
            mktac2 "__trytac" (fun uu____3253  -> FStar_Tactics_Basic.trytac)
              FStar_Syntax_Embeddings.e_any uu____3238 uu____3243
             in
          let uu____3254 =
            let uu____3257 =
              mktac1 "intro" FStar_Tactics_Basic.intro
                FStar_Syntax_Embeddings.e_unit
                FStar_Reflection_Embeddings.e_binder
               in
            let uu____3258 =
              let uu____3261 =
                let uu____3262 =
                  FStar_Syntax_Embeddings.e_tuple2
                    FStar_Reflection_Embeddings.e_binder
                    FStar_Reflection_Embeddings.e_binder
                   in
                mktac1 "intro_rec" FStar_Tactics_Basic.intro_rec
                  FStar_Syntax_Embeddings.e_unit uu____3262
                 in
              let uu____3273 =
                let uu____3276 =
                  let uu____3277 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Syntax_Embeddings.e_norm_step
                     in
                  mktac1 "norm" FStar_Tactics_Basic.norm uu____3277
                    FStar_Syntax_Embeddings.e_unit
                   in
                let uu____3284 =
                  let uu____3287 =
                    let uu____3288 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_norm_step
                       in
                    mktac3 "norm_term_env" FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Embeddings.e_env uu____3288
                      FStar_Reflection_Embeddings.e_term
                      FStar_Reflection_Embeddings.e_term
                     in
                  let uu____3295 =
                    let uu____3298 =
                      let uu____3299 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step
                         in
                      mktac2 "norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____3299
                        FStar_Reflection_Embeddings.e_binder
                        FStar_Syntax_Embeddings.e_unit
                       in
                    let uu____3306 =
                      let uu____3309 =
                        mktac2 "rename_to" FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_string
                          FStar_Syntax_Embeddings.e_unit
                         in
                      let uu____3310 =
                        let uu____3313 =
                          mktac1 "binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_unit
                           in
                        let uu____3314 =
                          let uu____3317 =
                            mktac1 "revert" FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Syntax_Embeddings.e_unit
                             in
                          let uu____3318 =
                            let uu____3321 =
                              mktac1 "clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit
                               in
                            let uu____3322 =
                              let uu____3325 =
                                mktac1 "clear" FStar_Tactics_Basic.clear
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                 in
                              let uu____3326 =
                                let uu____3329 =
                                  mktac1 "rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_unit
                                   in
                                let uu____3330 =
                                  let uu____3333 =
                                    mktac1 "smt" FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                     in
                                  let uu____3334 =
                                    let uu____3337 =
                                      mktac1 "refine_intro"
                                        FStar_Tactics_Basic.refine_intro
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                       in
                                    let uu____3338 =
                                      let uu____3341 =
                                        mktac2 "t_exact"
                                          FStar_Tactics_Basic.t_exact
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Syntax_Embeddings.e_unit
                                         in
                                      let uu____3342 =
                                        let uu____3345 =
                                          mktac1 "apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_unit
                                           in
                                        let uu____3346 =
                                          let uu____3349 =
                                            mktac1 "apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Embeddings.e_term
                                              FStar_Syntax_Embeddings.e_unit
                                             in
                                          let uu____3350 =
                                            let uu____3353 =
                                              mktac1 "apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Syntax_Embeddings.e_unit
                                               in
                                            let uu____3354 =
                                              let uu____3357 =
                                                let uu____3358 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____3363 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____3368 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Syntax_Embeddings.e_any
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                mktac5 "__divide"
                                                  (fun uu____3385  ->
                                                     fun uu____3386  ->
                                                       FStar_Tactics_Basic.divide)
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_int
                                                  uu____3358 uu____3363
                                                  uu____3368
                                                 in
                                              let uu____3387 =
                                                let uu____3390 =
                                                  let uu____3391 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____3396 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  mktac2 "__seq"
                                                    FStar_Tactics_Basic.seq
                                                    uu____3391 uu____3396
                                                    FStar_Syntax_Embeddings.e_unit
                                                   in
                                                let uu____3405 =
                                                  let uu____3408 =
                                                    mktac1 "set_options"
                                                      FStar_Tactics_Basic.set_options
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____3409 =
                                                    let uu____3412 =
                                                      mktac1 "tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Reflection_Embeddings.e_term
                                                       in
                                                    let uu____3413 =
                                                      let uu____3416 =
                                                        mktac1 "unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_unit
                                                         in
                                                      let uu____3417 =
                                                        let uu____3420 =
                                                          mktac2 "unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Reflection_Embeddings.e_term
                                                            FStar_Syntax_Embeddings.e_any
                                                           in
                                                        let uu____3421 =
                                                          let uu____3424 =
                                                            mktac1 "prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.e_string
                                                              FStar_Syntax_Embeddings.e_unit
                                                             in
                                                          let uu____3425 =
                                                            let uu____3428 =
                                                              mktac1 "addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____3429 =
                                                              let uu____3432
                                                                =
                                                                mktac1
                                                                  "print"
                                                                  FStar_Tactics_Basic.print
                                                                  FStar_Syntax_Embeddings.e_string
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                 in
                                                              let uu____3433
                                                                =
                                                                let uu____3436
                                                                  =
                                                                  mktac1
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                   in
                                                                let uu____3437
                                                                  =
                                                                  let uu____3440
                                                                    =
                                                                    mktac1
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                  let uu____3441
                                                                    =
                                                                    let uu____3444
                                                                    =
                                                                    mktac1
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3445
                                                                    =
                                                                    let uu____3448
                                                                    =
                                                                    let uu____3449
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____3449
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3456
                                                                    =
                                                                    let uu____3459
                                                                    =
                                                                    let uu____3460
                                                                    =
                                                                    let uu____3472
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____3472
                                                                     in
                                                                    let uu____3483
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    mktac2
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____3460
                                                                    uu____3483
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3499
                                                                    =
                                                                    let uu____3502
                                                                    =
                                                                    mktac1
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3503
                                                                    =
                                                                    let uu____3506
                                                                    =
                                                                    mktac1
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3507
                                                                    =
                                                                    let uu____3510
                                                                    =
                                                                    mktac1
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3511
                                                                    =
                                                                    let uu____3514
                                                                    =
                                                                    mktac1
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3515
                                                                    =
                                                                    let uu____3518
                                                                    =
                                                                    mktac1
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3519
                                                                    =
                                                                    let uu____3522
                                                                    =
                                                                    mktac1
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3523
                                                                    =
                                                                    let uu____3526
                                                                    =
                                                                    mktac1
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3527
                                                                    =
                                                                    let uu____3530
                                                                    =
                                                                    let uu____3531
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac1
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____3531
                                                                     in
                                                                    let uu____3542
                                                                    =
                                                                    let uu____3545
                                                                    =
                                                                    mktac1
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____3546
                                                                    =
                                                                    let uu____3549
                                                                    =
                                                                    mktac1
                                                                    "cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____3550
                                                                    =
                                                                    let uu____3553
                                                                    =
                                                                    mktac1
                                                                    "cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3554
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    mktac1
                                                                    "cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3558
                                                                    =
                                                                    let uu____3561
                                                                    =
                                                                    mktac1
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                     in
                                                                    let uu____3562
                                                                    =
                                                                    let uu____3565
                                                                    =
                                                                    mktac1
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3566
                                                                    =
                                                                    let uu____3569
                                                                    =
                                                                    mktac1
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____3570
                                                                    =
                                                                    let uu____3573
                                                                    =
                                                                    mktac1
                                                                    "ngoals"
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____3574
                                                                    =
                                                                    let uu____3577
                                                                    =
                                                                    mktac1
                                                                    "ngoals_smt"
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____3578
                                                                    =
                                                                    let uu____3581
                                                                    =
                                                                    mktac1
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____3582
                                                                    =
                                                                    let uu____3585
                                                                    =
                                                                    let uu____3586
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    mktac2
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____3586
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____3593
                                                                    =
                                                                    let uu____3596
                                                                    =
                                                                    mktac3
                                                                    "unify_env"
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____3597
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    let uu____3601
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    mktac3
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____3601
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____3608
                                                                    =
                                                                    let uu____3611
                                                                    =
                                                                    mktac2
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                     in
                                                                    let uu____3612
                                                                    =
                                                                    let uu____3615
                                                                    =
                                                                    mktac1
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____3616
                                                                    =
                                                                    let uu____3619
                                                                    =
                                                                    mktac1
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                     in
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3623
                                                                    =
                                                                    mktac1
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    [uu____3623;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____3619
                                                                    ::
                                                                    uu____3620
                                                                     in
                                                                    uu____3615
                                                                    ::
                                                                    uu____3616
                                                                     in
                                                                    uu____3611
                                                                    ::
                                                                    uu____3612
                                                                     in
                                                                    uu____3600
                                                                    ::
                                                                    uu____3608
                                                                     in
                                                                    uu____3596
                                                                    ::
                                                                    uu____3597
                                                                     in
                                                                    uu____3585
                                                                    ::
                                                                    uu____3593
                                                                     in
                                                                    uu____3581
                                                                    ::
                                                                    uu____3582
                                                                     in
                                                                    uu____3577
                                                                    ::
                                                                    uu____3578
                                                                     in
                                                                    uu____3573
                                                                    ::
                                                                    uu____3574
                                                                     in
                                                                    uu____3569
                                                                    ::
                                                                    uu____3570
                                                                     in
                                                                    uu____3565
                                                                    ::
                                                                    uu____3566
                                                                     in
                                                                    uu____3561
                                                                    ::
                                                                    uu____3562
                                                                     in
                                                                    uu____3557
                                                                    ::
                                                                    uu____3558
                                                                     in
                                                                    uu____3553
                                                                    ::
                                                                    uu____3554
                                                                     in
                                                                    uu____3549
                                                                    ::
                                                                    uu____3550
                                                                     in
                                                                    uu____3545
                                                                    ::
                                                                    uu____3546
                                                                     in
                                                                    uu____3530
                                                                    ::
                                                                    uu____3542
                                                                     in
                                                                    uu____3526
                                                                    ::
                                                                    uu____3527
                                                                     in
                                                                    uu____3522
                                                                    ::
                                                                    uu____3523
                                                                     in
                                                                    uu____3518
                                                                    ::
                                                                    uu____3519
                                                                     in
                                                                    uu____3514
                                                                    ::
                                                                    uu____3515
                                                                     in
                                                                    uu____3510
                                                                    ::
                                                                    uu____3511
                                                                     in
                                                                    uu____3506
                                                                    ::
                                                                    uu____3507
                                                                     in
                                                                    uu____3502
                                                                    ::
                                                                    uu____3503
                                                                     in
                                                                    uu____3459
                                                                    ::
                                                                    uu____3499
                                                                     in
                                                                    uu____3448
                                                                    ::
                                                                    uu____3456
                                                                     in
                                                                    uu____3444
                                                                    ::
                                                                    uu____3445
                                                                     in
                                                                  uu____3440
                                                                    ::
                                                                    uu____3441
                                                                   in
                                                                uu____3436 ::
                                                                  uu____3437
                                                                 in
                                                              uu____3432 ::
                                                                uu____3433
                                                               in
                                                            uu____3428 ::
                                                              uu____3429
                                                             in
                                                          uu____3424 ::
                                                            uu____3425
                                                           in
                                                        uu____3420 ::
                                                          uu____3421
                                                         in
                                                      uu____3416 ::
                                                        uu____3417
                                                       in
                                                    uu____3412 :: uu____3413
                                                     in
                                                  uu____3408 :: uu____3409
                                                   in
                                                uu____3390 :: uu____3405  in
                                              uu____3357 :: uu____3387  in
                                            uu____3353 :: uu____3354  in
                                          uu____3349 :: uu____3350  in
                                        uu____3345 :: uu____3346  in
                                      uu____3341 :: uu____3342  in
                                    uu____3337 :: uu____3338  in
                                  uu____3333 :: uu____3334  in
                                uu____3329 :: uu____3330  in
                              uu____3325 :: uu____3326  in
                            uu____3321 :: uu____3322  in
                          uu____3317 :: uu____3318  in
                        uu____3313 :: uu____3314  in
                      uu____3309 :: uu____3310  in
                    uu____3298 :: uu____3306  in
                  uu____3287 :: uu____3295  in
                uu____3276 :: uu____3284  in
              uu____3261 :: uu____3273  in
            uu____3257 :: uu____3258  in
          uu____3237 :: uu____3254  in
        uu____3233 :: uu____3234  in
      uu____3227 :: uu____3230  in
    FStar_List.append uu____3224
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)

and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            ('Aa -> 'Ar FStar_Tactics_Basic.tac)
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          FStar_Pervasives_Native.Some
            (fun x  ->
               let rng = FStar_Range.dummyRange  in
               let x_tm = FStar_Reflection_Interpreter.embed ea rng x ncb  in
               let app =
                 let uu____3651 =
                   let uu____3656 =
                     let uu____3657 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____3657]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____3656  in
                 uu____3651 FStar_Pervasives_Native.None rng  in
               unembed_tactic_0 er app ncb)

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun embedded_tac_b  ->
      fun ncb  ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state  ->
             let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
             let tm =
               let uu____3709 =
                 let uu____3714 =
                   let uu____3715 =
                     let uu____3724 =
                       FStar_Reflection_Interpreter.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____3724  in
                   [uu____3715]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3714  in
               uu____3709 FStar_Pervasives_Native.None rng  in
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
               (let uu____3749 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____3749)
             else ();
             (let result =
                let uu____3752 = primitive_steps ()  in
                FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                  uu____3752 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____3756 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____3756)
              else ();
              (let res =
                 let uu____3763 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Reflection_Interpreter.unembed uu____3763 result ncb
                  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____3778 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____3778
                     (fun uu____3782  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (msg,ps)) ->
                   let uu____3787 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____3787
                     (fun uu____3791  -> FStar_Tactics_Basic.fail msg)
               | FStar_Pervasives_Native.None  ->
                   let uu____3794 =
                     let uu____3799 =
                       let uu____3800 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____3800
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____3799)  in
                   FStar_Errors.raise_error uu____3794
                     (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      fun ncb  ->
        let uu____3810 = unembed_tactic_0 eb embedded_tac_b ncb  in
        FStar_All.pipe_left
          (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____3810

let report_implicits :
  'Auu____3829 . 'Auu____3829 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____3858 =
               let uu____3859 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____3860 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____3859 uu____3860 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____3858, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____3899 = FStar_ST.op_Bang tacdbg  in
             if uu____3899
             then
               let uu____3923 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "About to reduce uvars on: %s\n" uu____3923
             else ());
            (let tactic1 =
               FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic
                in
             (let uu____3927 = FStar_ST.op_Bang tacdbg  in
              if uu____3927
              then
                let uu____3951 = FStar_Syntax_Print.term_to_string tactic1
                   in
                FStar_Util.print1 "About to check tactic term: %s\n"
                  uu____3951
              else ());
             (let uu____3953 =
                FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
              match uu____3953 with
              | (uu____3966,uu____3967,g) ->
                  (FStar_TypeChecker_Rel.force_trivial_guard env g;
                   FStar_Errors.stop_if_err ();
                   (let tau =
                      unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic1
                        FStar_Syntax_Embeddings.id_norm_cb
                       in
                    let uu____3974 =
                      FStar_TypeChecker_Env.clear_expected_typ env  in
                    match uu____3974 with
                    | (env1,uu____3988) ->
                        let env2 =
                          let uu___344_3994 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___344_3994.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___344_3994.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___344_3994.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___344_3994.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___344_3994.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___344_3994.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___344_3994.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___344_3994.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___344_3994.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___344_3994.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___344_3994.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp = false;
                            FStar_TypeChecker_Env.effects =
                              (uu___344_3994.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___344_3994.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___344_3994.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___344_3994.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___344_3994.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___344_3994.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___344_3994.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___344_3994.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___344_3994.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___344_3994.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___344_3994.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___344_3994.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___344_3994.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___344_3994.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___344_3994.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___344_3994.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___344_3994.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___344_3994.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___344_3994.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___344_3994.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___344_3994.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___344_3994.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___344_3994.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___344_3994.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___344_3994.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___344_3994.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___344_3994.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___344_3994.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___344_3994.FStar_TypeChecker_Env.dep_graph)
                          }  in
                        let env3 =
                          let uu___345_3996 = env2  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___345_3996.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___345_3996.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___345_3996.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___345_3996.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___345_3996.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___345_3996.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___345_3996.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___345_3996.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___345_3996.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___345_3996.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___345_3996.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___345_3996.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___345_3996.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___345_3996.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___345_3996.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___345_3996.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___345_3996.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___345_3996.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___345_3996.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___345_3996.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___345_3996.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes = true;
                            FStar_TypeChecker_Env.phase1 =
                              (uu___345_3996.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___345_3996.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___345_3996.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___345_3996.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___345_3996.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___345_3996.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___345_3996.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___345_3996.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___345_3996.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___345_3996.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___345_3996.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___345_3996.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___345_3996.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___345_3996.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___345_3996.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___345_3996.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___345_3996.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___345_3996.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___345_3996.FStar_TypeChecker_Env.dep_graph)
                          }  in
                        let rng =
                          let uu____3998 = FStar_Range.use_range rng_goal  in
                          let uu____3999 = FStar_Range.use_range rng_tac  in
                          FStar_Range.range_of_rng uu____3998 uu____3999  in
                        let uu____4000 =
                          FStar_Tactics_Basic.proofstate_of_goal_ty rng env3
                            typ
                           in
                        (match uu____4000 with
                         | (ps,w) ->
                             ((let uu____4014 = FStar_ST.op_Bang tacdbg  in
                               if uu____4014
                               then
                                 let uu____4038 =
                                   FStar_Syntax_Print.term_to_string typ  in
                                 FStar_Util.print1
                                   "Running tactic with goal = %s\n"
                                   uu____4038
                               else ());
                              (let uu____4040 =
                                 FStar_Util.record_time
                                   (fun uu____4050  ->
                                      FStar_Tactics_Basic.run tau ps)
                                  in
                               match uu____4040 with
                               | (res,ms) ->
                                   ((let uu____4064 = FStar_ST.op_Bang tacdbg
                                        in
                                     if uu____4064
                                     then
                                       let uu____4088 =
                                         FStar_Syntax_Print.term_to_string
                                           tactic1
                                          in
                                       let uu____4089 =
                                         FStar_Util.string_of_int ms  in
                                       let uu____4090 =
                                         FStar_Syntax_Print.lid_to_string
                                           env3.FStar_TypeChecker_Env.curmodule
                                          in
                                       FStar_Util.print3
                                         "Tactic %s ran in %s ms (%s)\n"
                                         uu____4088 uu____4089 uu____4090
                                     else ());
                                    (match res with
                                     | FStar_Tactics_Result.Success
                                         (uu____4098,ps1) ->
                                         ((let uu____4101 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____4101
                                           then
                                             let uu____4125 =
                                               FStar_Syntax_Print.term_to_string
                                                 w
                                                in
                                             FStar_Util.print1
                                               "Tactic generated proofterm %s\n"
                                               uu____4125
                                           else ());
                                          FStar_List.iter
                                            (fun g1  ->
                                               let uu____4132 =
                                                 FStar_Tactics_Basic.is_irrelevant
                                                   g1
                                                  in
                                               if uu____4132
                                               then
                                                 let uu____4133 =
                                                   let uu____4134 =
                                                     FStar_Tactics_Types.goal_env
                                                       g1
                                                      in
                                                   let uu____4135 =
                                                     FStar_Tactics_Types.goal_witness
                                                       g1
                                                      in
                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                     uu____4134 uu____4135
                                                     FStar_Syntax_Util.exp_unit
                                                    in
                                                 (if uu____4133
                                                  then ()
                                                  else
                                                    (let uu____4137 =
                                                       let uu____4138 =
                                                         let uu____4139 =
                                                           FStar_Tactics_Types.goal_witness
                                                             g1
                                                            in
                                                         FStar_Syntax_Print.term_to_string
                                                           uu____4139
                                                          in
                                                       FStar_Util.format1
                                                         "Irrelevant tactic witness does not unify with (): %s"
                                                         uu____4138
                                                        in
                                                     failwith uu____4137))
                                               else ())
                                            (FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals);
                                          (let uu____4142 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____4142
                                           then
                                             let uu____4166 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print1
                                               "About to check tactic implicits: %s\n"
                                               uu____4166
                                           else ());
                                          (let g1 =
                                             let uu___346_4171 =
                                               FStar_TypeChecker_Env.trivial_guard
                                                in
                                             {
                                               FStar_TypeChecker_Env.guard_f
                                                 =
                                                 (uu___346_4171.FStar_TypeChecker_Env.guard_f);
                                               FStar_TypeChecker_Env.deferred
                                                 =
                                                 (uu___346_4171.FStar_TypeChecker_Env.deferred);
                                               FStar_TypeChecker_Env.univ_ineqs
                                                 =
                                                 (uu___346_4171.FStar_TypeChecker_Env.univ_ineqs);
                                               FStar_TypeChecker_Env.implicits
                                                 =
                                                 (ps1.FStar_Tactics_Types.all_implicits)
                                             }  in
                                           let g2 =
                                             FStar_TypeChecker_Rel.solve_deferred_constraints
                                               env3 g1
                                              in
                                           (let uu____4174 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____4174
                                            then
                                              let uu____4198 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print1
                                                "Checked (1) implicits: %s\n"
                                                uu____4198
                                            else ());
                                           (let g3 =
                                              FStar_TypeChecker_Rel.resolve_implicits_tac
                                                env3 g2
                                               in
                                            (let uu____4204 =
                                               FStar_ST.op_Bang tacdbg  in
                                             if uu____4204
                                             then
                                               let uu____4228 =
                                                 FStar_Common.string_of_list
                                                   (fun imp  ->
                                                      FStar_Syntax_Print.ctx_uvar_to_string
                                                        imp.FStar_TypeChecker_Env.imp_uvar)
                                                   ps1.FStar_Tactics_Types.all_implicits
                                                  in
                                               FStar_Util.print1
                                                 "Checked (2) implicits: %s\n"
                                                 uu____4228
                                             else ());
                                            report_implicits ps1
                                              g3.FStar_TypeChecker_Env.implicits;
                                            ((FStar_List.append
                                                ps1.FStar_Tactics_Types.goals
                                                ps1.FStar_Tactics_Types.smt_goals),
                                              w))))
                                     | FStar_Tactics_Result.Failed (s,ps1) ->
                                         ((let uu____4238 =
                                             let uu____4239 =
                                               FStar_TypeChecker_Normalize.psc_subst
                                                 ps1.FStar_Tactics_Types.psc
                                                in
                                             FStar_Tactics_Types.subst_proof_state
                                               uu____4239 ps1
                                              in
                                           FStar_Tactics_Basic.dump_proofstate
                                             uu____4238
                                             "at the time of failure");
                                          (let uu____4240 =
                                             let uu____4245 =
                                               FStar_Util.format1
                                                 "user tactic failed: %s" s
                                                in
                                             (FStar_Errors.Fatal_UserTacticFailure,
                                               uu____4245)
                                              in
                                           FStar_Errors.raise_error
                                             uu____4240
                                             ps1.FStar_Tactics_Types.entry_range)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____4257 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____4263 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____4269 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____4324 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____4364 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____4418 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____4459 . 'Auu____4459 -> 'Auu____4459 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____4487 = FStar_Syntax_Util.head_and_args t  in
        match uu____4487 with
        | (hd1,args) ->
            let uu____4530 =
              let uu____4545 =
                let uu____4546 = FStar_Syntax_Util.un_uinst hd1  in
                uu____4546.FStar_Syntax_Syntax.n  in
              (uu____4545, args)  in
            (match uu____4530 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____4561))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____4624 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____4624 with
                       | (gs,uu____4632) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____4639 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____4639 with
                       | (gs,uu____4647) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____4690 =
                        let uu____4697 =
                          let uu____4700 =
                            let uu____4701 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____4701
                             in
                          [uu____4700]  in
                        (FStar_Syntax_Util.t_true, uu____4697)  in
                      Simplified uu____4690
                  | Both  ->
                      let uu____4712 =
                        let uu____4721 =
                          let uu____4724 =
                            let uu____4725 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____4725
                             in
                          [uu____4724]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____4721)  in
                      Dual uu____4712
                  | Neg  -> Simplified (assertion, []))
             | uu____4738 -> Unchanged t)
  
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
    fun uu___343_4828  ->
      match uu___343_4828 with
      | Unchanged t -> let uu____4834 = f t  in Unchanged uu____4834
      | Simplified (t,gs) ->
          let uu____4841 = let uu____4848 = f t  in (uu____4848, gs)  in
          Simplified uu____4841
      | Dual (tn,tp,gs) ->
          let uu____4858 =
            let uu____4867 = f tn  in
            let uu____4868 = f tp  in (uu____4867, uu____4868, gs)  in
          Dual uu____4858
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____4931 = f t1 t2  in Unchanged uu____4931
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____4943 = let uu____4950 = f t1 t2  in (uu____4950, gs)
               in
            Simplified uu____4943
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____4964 = let uu____4971 = f t1 t2  in (uu____4971, gs)
               in
            Simplified uu____4964
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____4990 =
              let uu____4997 = f t1 t2  in
              (uu____4997, (FStar_List.append gs1 gs2))  in
            Simplified uu____4990
        | uu____5000 ->
            let uu____5009 = explode x  in
            (match uu____5009 with
             | (n1,p1,gs1) ->
                 let uu____5027 = explode y  in
                 (match uu____5027 with
                  | (n2,p2,gs2) ->
                      let uu____5045 =
                        let uu____5054 = f n1 n2  in
                        let uu____5055 = f p1 p2  in
                        (uu____5054, uu____5055, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____5045))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____5127 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____5127
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____5175  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____5217 =
              let uu____5218 = FStar_Syntax_Subst.compress t  in
              uu____5218.FStar_Syntax_Syntax.n  in
            match uu____5217 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____5230 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____5230 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____5256 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____5256 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____5276;
                   FStar_Syntax_Syntax.vars = uu____5277;_},(p,uu____5279)::
                 (q,uu____5281)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____5337 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5337
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____5340 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____5340 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____5354 = FStar_Syntax_Util.mk_imp l r  in
                       uu____5354.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____5358;
                   FStar_Syntax_Syntax.vars = uu____5359;_},(p,uu____5361)::
                 (q,uu____5363)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____5419 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5419
                   in
                let xq =
                  let uu____5421 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____5421
                   in
                let r1 =
                  let uu____5423 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____5423 p  in
                let r2 =
                  let uu____5425 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____5425 q  in
                (match (r1, r2) with
                 | (Unchanged uu____5432,Unchanged uu____5433) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____5451 = FStar_Syntax_Util.mk_iff l r  in
                            uu____5451.FStar_Syntax_Syntax.n) r1 r2
                 | uu____5454 ->
                     let uu____5463 = explode r1  in
                     (match uu____5463 with
                      | (pn,pp,gs1) ->
                          let uu____5481 = explode r2  in
                          (match uu____5481 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____5502 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____5505 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____5502
                                   uu____5505
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____5569  ->
                       fun r  ->
                         match uu____5569 with
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
                let uu____5721 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____5721 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____5761  ->
                            match uu____5761 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____5783 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___347_5815 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___347_5815.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___347_5815.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____5783 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____5843 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____5843.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____5889 = traverse f pol e t1  in
                let uu____5894 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____5894 uu____5889
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___348_5934 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___348_5934.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___348_5934.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____5941 =
                f pol e
                  (let uu___349_5945 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___349_5945.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___349_5945.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____5941
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___350_5955 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___350_5955.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___350_5955.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____5956 = explode rp  in
              (match uu____5956 with
               | (uu____5965,p',gs') ->
                   Dual
                     ((let uu___351_5975 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___351_5975.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___351_5975.FStar_Syntax_Syntax.vars)
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
      (let uu____6018 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____6018);
      (let uu____6043 = FStar_ST.op_Bang tacdbg  in
       if uu____6043
       then
         let uu____6067 =
           let uu____6068 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____6068
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____6069 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____6067
           uu____6069
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____6098 =
         let uu____6107 = traverse by_tactic_interp Pos env goal  in
         match uu____6107 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____6131 -> failwith "no"  in
       match uu____6098 with
       | (t',gs) ->
           ((let uu____6159 = FStar_ST.op_Bang tacdbg  in
             if uu____6159
             then
               let uu____6183 =
                 let uu____6184 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____6184
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____6185 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____6183 uu____6185
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____6233  ->
                    fun g  ->
                      match uu____6233 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____6278 =
                              let uu____6281 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____6282 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____6281 uu____6282  in
                            match uu____6278 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____6283 =
                                  let uu____6288 =
                                    let uu____6289 =
                                      let uu____6290 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____6290
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____6289
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____6288)
                                   in
                                FStar_Errors.raise_error uu____6283
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____6293 = FStar_ST.op_Bang tacdbg  in
                            if uu____6293
                            then
                              let uu____6317 = FStar_Util.string_of_int n1
                                 in
                              let uu____6318 =
                                let uu____6319 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____6319
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____6317 uu____6318
                            else ());
                           (let gt' =
                              let uu____6322 =
                                let uu____6323 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____6323
                                 in
                              FStar_TypeChecker_Util.label uu____6322
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____6324 =
                              let uu____6333 =
                                let uu____6340 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____6340, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____6333 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____6324)))) s
                 gs
                in
             let uu____6355 = s1  in
             match uu____6355 with
             | (uu____6376,gs1) ->
                 let uu____6394 =
                   let uu____6401 = FStar_Options.peek ()  in
                   (env, t', uu____6401)  in
                 uu____6394 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____6414 =
        let uu____6415 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____6415  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____6414 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____6416 =
      let uu____6421 =
        let uu____6422 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____6431 =
          let uu____6442 = FStar_Syntax_Syntax.as_arg a  in [uu____6442]  in
        uu____6422 :: uu____6431  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____6421  in
    uu____6416 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
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
          let uu____6492 =
            let uu____6497 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____6498 =
              let uu____6499 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6499]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____6497 uu____6498  in
          uu____6492 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____6528 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____6528);
           (let uu____6552 =
              let uu____6559 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____6559 env typ
               in
            match uu____6552 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____6573 =
                        let uu____6576 = FStar_Tactics_Types.goal_env g  in
                        let uu____6577 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____6576 uu____6577  in
                      match uu____6573 with
                      | FStar_Pervasives_Native.Some vc ->
                          let guard =
                            {
                              FStar_TypeChecker_Env.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Env.deferred = [];
                              FStar_TypeChecker_Env.univ_ineqs = ([], []);
                              FStar_TypeChecker_Env.implicits = []
                            }  in
                          let uu____6588 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____6588 guard
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
      (let uu____6604 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____6604);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____6629 =
         let uu____6636 = reify_tactic tau  in
         run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
           tau.FStar_Syntax_Syntax.pos uu____6636 env typ
          in
       match uu____6629 with
       | (gs,w) ->
           ((let uu____6646 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____6650 =
                      let uu____6651 =
                        let uu____6654 = FStar_Tactics_Types.goal_env g  in
                        let uu____6655 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____6654 uu____6655  in
                      FStar_Option.isSome uu____6651  in
                    Prims.op_Negation uu____6650) gs
                in
             if uu____6646
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
             let uu____6658 =
               let uu____6663 =
                 FStar_Syntax_Embeddings.e_list
                   FStar_Reflection_Embeddings.e_sigelt
                  in
               FStar_Reflection_Interpreter.unembed uu____6663 w1
                 FStar_Syntax_Embeddings.id_norm_cb
                in
             match uu____6658 with
             | FStar_Pervasives_Native.Some sigelts -> sigelts
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SpliceUnembedFail,
                     "splice: failed to unembed sigelts")
                   typ.FStar_Syntax_Syntax.pos)))
  