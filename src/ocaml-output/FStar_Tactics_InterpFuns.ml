open Prims
let extract_1 :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.args -> 'a FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun args  ->
      match args with
      | (a,uu____25)::[] ->
          let uu____50 = FStar_Syntax_Embeddings.unembed ea a  in
          FStar_Util.bind_opt uu____50
            (fun a1  -> FStar_Pervasives_Native.Some a1)
      | uu____55 -> failwith "extract_1: wrong number of arguments"
  
let extract_2 :
  'a 'b .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.args ->
          ('a,'b) FStar_Pervasives_Native.tuple2
            FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun args  ->
        match args with
        | (a,uu____100)::(b,uu____102)::[] ->
            let uu____143 = FStar_Syntax_Embeddings.unembed ea a  in
            FStar_Util.bind_opt uu____143
              (fun a1  ->
                 let uu____153 = FStar_Syntax_Embeddings.unembed eb b  in
                 FStar_Util.bind_opt uu____153
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____166 -> failwith "extract_2: wrong number of arguments"
  
let extract_3 :
  'a 'b 'c .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          FStar_Syntax_Syntax.args ->
            ('a,'b,'c) FStar_Pervasives_Native.tuple3
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun args  ->
          match args with
          | (a,uu____231)::(b,uu____233)::(c,uu____235)::[] ->
              let uu____292 = FStar_Syntax_Embeddings.unembed ea a  in
              FStar_Util.bind_opt uu____292
                (fun a1  ->
                   let uu____304 = FStar_Syntax_Embeddings.unembed eb b  in
                   FStar_Util.bind_opt uu____304
                     (fun b1  ->
                        let uu____316 = FStar_Syntax_Embeddings.unembed ec c
                           in
                        FStar_Util.bind_opt uu____316
                          (fun c1  ->
                             FStar_Pervasives_Native.Some (a1, b1, c1))))
          | uu____333 -> failwith "extract_3: wrong number of arguments"
  
let extract_4 :
  'a 'b 'c 'd .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            FStar_Syntax_Syntax.args ->
              ('a,'b,'c,'d) FStar_Pervasives_Native.tuple4
                FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun args  ->
            match args with
            | (a,uu____416)::(b,uu____418)::(c,uu____420)::(d,uu____422)::[]
                ->
                let uu____495 = FStar_Syntax_Embeddings.unembed ea a  in
                FStar_Util.bind_opt uu____495
                  (fun a1  ->
                     let uu____509 = FStar_Syntax_Embeddings.unembed eb b  in
                     FStar_Util.bind_opt uu____509
                       (fun b1  ->
                          let uu____523 =
                            FStar_Syntax_Embeddings.unembed ec c  in
                          FStar_Util.bind_opt uu____523
                            (fun c1  ->
                               let uu____537 =
                                 FStar_Syntax_Embeddings.unembed ed d  in
                               FStar_Util.bind_opt uu____537
                                 (fun d1  ->
                                    FStar_Pervasives_Native.Some
                                      (a1, b1, c1, d1)))))
            | uu____558 -> failwith "extract_4: wrong number of arguments"
  
let extract_5 :
  'a 'b 'c 'd 'e .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            'e FStar_Syntax_Embeddings.embedding ->
              FStar_Syntax_Syntax.args ->
                ('a,'b,'c,'d,'e) FStar_Pervasives_Native.tuple5
                  FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ee  ->
            fun args  ->
              match args with
              | (a,uu____659)::(b,uu____661)::(c,uu____663)::(d,uu____665)::
                  (e,uu____667)::[] ->
                  let uu____756 = FStar_Syntax_Embeddings.unembed ea a  in
                  FStar_Util.bind_opt uu____756
                    (fun a1  ->
                       let uu____772 = FStar_Syntax_Embeddings.unembed eb b
                          in
                       FStar_Util.bind_opt uu____772
                         (fun b1  ->
                            let uu____788 =
                              FStar_Syntax_Embeddings.unembed ec c  in
                            FStar_Util.bind_opt uu____788
                              (fun c1  ->
                                 let uu____804 =
                                   FStar_Syntax_Embeddings.unembed ed d  in
                                 FStar_Util.bind_opt uu____804
                                   (fun d1  ->
                                      let uu____820 =
                                        FStar_Syntax_Embeddings.unembed ee e
                                         in
                                      FStar_Util.bind_opt uu____820
                                        (fun e1  ->
                                           FStar_Pervasives_Native.Some
                                             (a1, b1, c1, d1, e1))))))
              | uu____845 -> failwith "extract_5: wrong number of arguments"
  
let extract_6 :
  'a 'b 'c 'd 'e 'f .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            'e FStar_Syntax_Embeddings.embedding ->
              'f FStar_Syntax_Embeddings.embedding ->
                FStar_Syntax_Syntax.args ->
                  ('a,'b,'c,'d,'e,'f) FStar_Pervasives_Native.tuple6
                    FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ee  ->
            fun ef  ->
              fun args  ->
                match args with
                | (a,uu____964)::(b,uu____966)::(c,uu____968)::(d,uu____970)::
                    (e,uu____972)::(f,uu____974)::[] ->
                    let uu____1079 = FStar_Syntax_Embeddings.unembed ea a  in
                    FStar_Util.bind_opt uu____1079
                      (fun a1  ->
                         let uu____1097 =
                           FStar_Syntax_Embeddings.unembed eb b  in
                         FStar_Util.bind_opt uu____1097
                           (fun b1  ->
                              let uu____1115 =
                                FStar_Syntax_Embeddings.unembed ec c  in
                              FStar_Util.bind_opt uu____1115
                                (fun c1  ->
                                   let uu____1133 =
                                     FStar_Syntax_Embeddings.unembed ed d  in
                                   FStar_Util.bind_opt uu____1133
                                     (fun d1  ->
                                        let uu____1151 =
                                          FStar_Syntax_Embeddings.unembed ee
                                            e
                                           in
                                        FStar_Util.bind_opt uu____1151
                                          (fun e1  ->
                                             let uu____1169 =
                                               FStar_Syntax_Embeddings.unembed
                                                 ef f
                                                in
                                             FStar_Util.bind_opt uu____1169
                                               (fun f1  ->
                                                  FStar_Pervasives_Native.Some
                                                    (a1, b1, c1, d1, e1, f1)))))))
                | uu____1198 ->
                    failwith "extract_6: wrong number of arguments"
  
let extract_7 :
  'a 'b 'c 'd 'e 'f 'g .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            'e FStar_Syntax_Embeddings.embedding ->
              'f FStar_Syntax_Embeddings.embedding ->
                'g FStar_Syntax_Embeddings.embedding ->
                  FStar_Syntax_Syntax.args ->
                    ('a,'b,'c,'d,'e,'f,'g) FStar_Pervasives_Native.tuple7
                      FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ee  ->
            fun ef  ->
              fun eg  ->
                fun args  ->
                  match args with
                  | (a,uu____1335)::(b,uu____1337)::(c,uu____1339)::(d,uu____1341)::
                      (e,uu____1343)::(f,uu____1345)::(g,uu____1347)::[] ->
                      let uu____1468 = FStar_Syntax_Embeddings.unembed ea a
                         in
                      FStar_Util.bind_opt uu____1468
                        (fun a1  ->
                           let uu____1488 =
                             FStar_Syntax_Embeddings.unembed eb b  in
                           FStar_Util.bind_opt uu____1488
                             (fun b1  ->
                                let uu____1508 =
                                  FStar_Syntax_Embeddings.unembed ec c  in
                                FStar_Util.bind_opt uu____1508
                                  (fun c1  ->
                                     let uu____1528 =
                                       FStar_Syntax_Embeddings.unembed ed d
                                        in
                                     FStar_Util.bind_opt uu____1528
                                       (fun d1  ->
                                          let uu____1548 =
                                            FStar_Syntax_Embeddings.unembed
                                              ee e
                                             in
                                          FStar_Util.bind_opt uu____1548
                                            (fun e1  ->
                                               let uu____1568 =
                                                 FStar_Syntax_Embeddings.unembed
                                                   ef f
                                                  in
                                               FStar_Util.bind_opt uu____1568
                                                 (fun f1  ->
                                                    let uu____1588 =
                                                      FStar_Syntax_Embeddings.unembed
                                                        eg g
                                                       in
                                                    FStar_Util.bind_opt
                                                      uu____1588
                                                      (fun g1  ->
                                                         FStar_Pervasives_Native.Some
                                                           (a1, b1, c1, d1,
                                                             e1, f1, g1))))))))
                  | uu____1621 ->
                      failwith "extract_7: wrong number of arguments"
  
let extract_1_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.args -> 'a FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun args  ->
      match args with
      | (a,uu____1662)::[] ->
          let uu____1671 = FStar_TypeChecker_NBETerm.unembed ea a  in
          FStar_Util.bind_opt uu____1671
            (fun a1  -> FStar_Pervasives_Native.Some a1)
      | uu____1676 -> failwith "extract_1_nbe: wrong number of arguments"
  
let extract_2_nbe :
  'a 'b .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'b FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.args ->
          ('a,'b) FStar_Pervasives_Native.tuple2
            FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun args  ->
        match args with
        | (a,uu____1721)::(b,uu____1723)::[] ->
            let uu____1736 = FStar_TypeChecker_NBETerm.unembed ea a  in
            FStar_Util.bind_opt uu____1736
              (fun a1  ->
                 let uu____1746 = FStar_TypeChecker_NBETerm.unembed eb b  in
                 FStar_Util.bind_opt uu____1746
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____1759 -> failwith "extract_2_nbe: wrong number of arguments"
  
let extract_3_nbe :
  'a 'b 'c .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'b FStar_TypeChecker_NBETerm.embedding ->
        'c FStar_TypeChecker_NBETerm.embedding ->
          FStar_TypeChecker_NBETerm.args ->
            ('a,'b,'c) FStar_Pervasives_Native.tuple3
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun args  ->
          match args with
          | (a,uu____1824)::(b,uu____1826)::(c,uu____1828)::[] ->
              let uu____1845 = FStar_TypeChecker_NBETerm.unembed ea a  in
              FStar_Util.bind_opt uu____1845
                (fun a1  ->
                   let uu____1857 = FStar_TypeChecker_NBETerm.unembed eb b
                      in
                   FStar_Util.bind_opt uu____1857
                     (fun b1  ->
                        let uu____1869 =
                          FStar_TypeChecker_NBETerm.unembed ec c  in
                        FStar_Util.bind_opt uu____1869
                          (fun c1  ->
                             FStar_Pervasives_Native.Some (a1, b1, c1))))
          | uu____1886 -> failwith "extract_3_nbe: wrong number of arguments"
  
let extract_4_nbe :
  'a 'b 'c 'd .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'b FStar_TypeChecker_NBETerm.embedding ->
        'c FStar_TypeChecker_NBETerm.embedding ->
          'd FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              ('a,'b,'c,'d) FStar_Pervasives_Native.tuple4
                FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun args  ->
            match args with
            | (a,uu____1969)::(b,uu____1971)::(c,uu____1973)::(d,uu____1975)::[]
                ->
                let uu____1996 = FStar_TypeChecker_NBETerm.unembed ea a  in
                FStar_Util.bind_opt uu____1996
                  (fun a1  ->
                     let uu____2010 = FStar_TypeChecker_NBETerm.unembed eb b
                        in
                     FStar_Util.bind_opt uu____2010
                       (fun b1  ->
                          let uu____2024 =
                            FStar_TypeChecker_NBETerm.unembed ec c  in
                          FStar_Util.bind_opt uu____2024
                            (fun c1  ->
                               let uu____2038 =
                                 FStar_TypeChecker_NBETerm.unembed ed d  in
                               FStar_Util.bind_opt uu____2038
                                 (fun d1  ->
                                    FStar_Pervasives_Native.Some
                                      (a1, b1, c1, d1)))))
            | uu____2059 ->
                failwith "extract_4_nbe: wrong number of arguments"
  
let extract_5_nbe :
  'a 'b 'c 'd 'e .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'b FStar_TypeChecker_NBETerm.embedding ->
        'c FStar_TypeChecker_NBETerm.embedding ->
          'd FStar_TypeChecker_NBETerm.embedding ->
            'e FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.args ->
                ('a,'b,'c,'d,'e) FStar_Pervasives_Native.tuple5
                  FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ee  ->
            fun args  ->
              match args with
              | (a,uu____2160)::(b,uu____2162)::(c,uu____2164)::(d,uu____2166)::
                  (e,uu____2168)::[] ->
                  let uu____2193 = FStar_TypeChecker_NBETerm.unembed ea a  in
                  FStar_Util.bind_opt uu____2193
                    (fun a1  ->
                       let uu____2209 =
                         FStar_TypeChecker_NBETerm.unembed eb b  in
                       FStar_Util.bind_opt uu____2209
                         (fun b1  ->
                            let uu____2225 =
                              FStar_TypeChecker_NBETerm.unembed ec c  in
                            FStar_Util.bind_opt uu____2225
                              (fun c1  ->
                                 let uu____2241 =
                                   FStar_TypeChecker_NBETerm.unembed ed d  in
                                 FStar_Util.bind_opt uu____2241
                                   (fun d1  ->
                                      let uu____2257 =
                                        FStar_TypeChecker_NBETerm.unembed ee
                                          e
                                         in
                                      FStar_Util.bind_opt uu____2257
                                        (fun e1  ->
                                           FStar_Pervasives_Native.Some
                                             (a1, b1, c1, d1, e1))))))
              | uu____2282 ->
                  failwith "extract_5_nbe: wrong number of arguments"
  
let extract_6_nbe :
  'a 'b 'c 'd 'e 'f .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'b FStar_TypeChecker_NBETerm.embedding ->
        'c FStar_TypeChecker_NBETerm.embedding ->
          'd FStar_TypeChecker_NBETerm.embedding ->
            'e FStar_TypeChecker_NBETerm.embedding ->
              'f FStar_TypeChecker_NBETerm.embedding ->
                FStar_TypeChecker_NBETerm.args ->
                  ('a,'b,'c,'d,'e,'f) FStar_Pervasives_Native.tuple6
                    FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ee  ->
            fun ef  ->
              fun args  ->
                match args with
                | (a,uu____2401)::(b,uu____2403)::(c,uu____2405)::(d,uu____2407)::
                    (e,uu____2409)::(f,uu____2411)::[] ->
                    let uu____2440 = FStar_TypeChecker_NBETerm.unembed ea a
                       in
                    FStar_Util.bind_opt uu____2440
                      (fun a1  ->
                         let uu____2458 =
                           FStar_TypeChecker_NBETerm.unembed eb b  in
                         FStar_Util.bind_opt uu____2458
                           (fun b1  ->
                              let uu____2476 =
                                FStar_TypeChecker_NBETerm.unembed ec c  in
                              FStar_Util.bind_opt uu____2476
                                (fun c1  ->
                                   let uu____2494 =
                                     FStar_TypeChecker_NBETerm.unembed ed d
                                      in
                                   FStar_Util.bind_opt uu____2494
                                     (fun d1  ->
                                        let uu____2512 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            ee e
                                           in
                                        FStar_Util.bind_opt uu____2512
                                          (fun e1  ->
                                             let uu____2530 =
                                               FStar_TypeChecker_NBETerm.unembed
                                                 ef f
                                                in
                                             FStar_Util.bind_opt uu____2530
                                               (fun f1  ->
                                                  FStar_Pervasives_Native.Some
                                                    (a1, b1, c1, d1, e1, f1)))))))
                | uu____2559 ->
                    failwith "extract_6_nbe: wrong number of arguments"
  
let extract_7_nbe :
  'a 'b 'c 'd 'e 'f 'g .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'b FStar_TypeChecker_NBETerm.embedding ->
        'c FStar_TypeChecker_NBETerm.embedding ->
          'd FStar_TypeChecker_NBETerm.embedding ->
            'e FStar_TypeChecker_NBETerm.embedding ->
              'f FStar_TypeChecker_NBETerm.embedding ->
                'g FStar_TypeChecker_NBETerm.embedding ->
                  FStar_TypeChecker_NBETerm.args ->
                    ('a,'b,'c,'d,'e,'f,'g) FStar_Pervasives_Native.tuple7
                      FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ee  ->
            fun ef  ->
              fun eg  ->
                fun args  ->
                  match args with
                  | (a,uu____2696)::(b,uu____2698)::(c,uu____2700)::(d,uu____2702)::
                      (e,uu____2704)::(f,uu____2706)::(g,uu____2708)::[] ->
                      let uu____2741 = FStar_TypeChecker_NBETerm.unembed ea a
                         in
                      FStar_Util.bind_opt uu____2741
                        (fun a1  ->
                           let uu____2761 =
                             FStar_TypeChecker_NBETerm.unembed eb b  in
                           FStar_Util.bind_opt uu____2761
                             (fun b1  ->
                                let uu____2781 =
                                  FStar_TypeChecker_NBETerm.unembed ec c  in
                                FStar_Util.bind_opt uu____2781
                                  (fun c1  ->
                                     let uu____2801 =
                                       FStar_TypeChecker_NBETerm.unembed ed d
                                        in
                                     FStar_Util.bind_opt uu____2801
                                       (fun d1  ->
                                          let uu____2821 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              ee e
                                             in
                                          FStar_Util.bind_opt uu____2821
                                            (fun e1  ->
                                               let uu____2841 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   ef f
                                                  in
                                               FStar_Util.bind_opt uu____2841
                                                 (fun f1  ->
                                                    let uu____2861 =
                                                      FStar_TypeChecker_NBETerm.unembed
                                                        eg g
                                                       in
                                                    FStar_Util.bind_opt
                                                      uu____2861
                                                      (fun g1  ->
                                                         FStar_Pervasives_Native.Some
                                                           (a1, b1, c1, d1,
                                                             e1, f1, g1))))))))
                  | uu____2894 ->
                      failwith "extract_7_nbe: wrong number of arguments"
  
let mk_tactic_interpretation_1 :
  'a 'r .
    ('a -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'r FStar_Syntax_Embeddings.embedding ->
          FStar_TypeChecker_Cfg.psc ->
            FStar_Syntax_Syntax.args ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun er  ->
        fun psc  ->
          fun args  ->
            let uu____2971 =
              extract_2 ea FStar_Tactics_Embedding.e_proofstate args  in
            FStar_Util.bind_opt uu____2971
              (fun uu____2988  ->
                 match uu____2988 with
                 | (a,ps) ->
                     let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                     let r =
                       let uu____3001 = t a  in
                       FStar_Tactics_Basic.run_safe uu____3001 ps1  in
                     let uu____3004 =
                       let uu____3005 = FStar_Tactics_Embedding.e_result er
                          in
                       let uu____3010 = FStar_TypeChecker_Cfg.psc_range psc
                          in
                       FStar_Syntax_Embeddings.embed uu____3005 uu____3010 r
                        in
                     FStar_Pervasives_Native.Some uu____3004)
  
let mk_tactic_interpretation_2 :
  'a 'b 'r .
    ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_TypeChecker_Cfg.psc ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun er  ->
          fun psc  ->
            fun args  ->
              let uu____3092 =
                extract_3 ea eb FStar_Tactics_Embedding.e_proofstate args  in
              FStar_Util.bind_opt uu____3092
                (fun uu____3114  ->
                   match uu____3114 with
                   | (a,b,ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let r =
                         let uu____3130 = t a b  in
                         FStar_Tactics_Basic.run_safe uu____3130 ps1  in
                       let uu____3133 =
                         let uu____3134 = FStar_Tactics_Embedding.e_result er
                            in
                         let uu____3139 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         FStar_Syntax_Embeddings.embed uu____3134 uu____3139
                           r
                          in
                       FStar_Pervasives_Native.Some uu____3133)
  
let mk_tactic_interpretation_3 :
  'a 'b 'c 'r .
    ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'c FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_TypeChecker_Cfg.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun er  ->
            fun psc  ->
              fun args  ->
                let uu____3240 =
                  extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                    args
                   in
                FStar_Util.bind_opt uu____3240
                  (fun uu____3267  ->
                     match uu____3267 with
                     | (a,b,c,ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let r =
                           let uu____3286 = t a b c  in
                           FStar_Tactics_Basic.run_safe uu____3286 ps1  in
                         let uu____3289 =
                           let uu____3290 =
                             FStar_Tactics_Embedding.e_result er  in
                           let uu____3295 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           FStar_Syntax_Embeddings.embed uu____3290
                             uu____3295 r
                            in
                         FStar_Pervasives_Native.Some uu____3289)
  
let mk_tactic_interpretation_4 :
  'a 'b 'c 'd 'r .
    ('a -> 'b -> 'c -> 'd -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'c FStar_Syntax_Embeddings.embedding ->
            'd FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                FStar_TypeChecker_Cfg.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun er  ->
              fun psc  ->
                fun args  ->
                  let uu____3415 =
                    extract_5 ea eb ec ed
                      FStar_Tactics_Embedding.e_proofstate args
                     in
                  FStar_Util.bind_opt uu____3415
                    (fun uu____3447  ->
                       match uu____3447 with
                       | (a,b,c,d,ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let r =
                             let uu____3469 = t a b c d  in
                             FStar_Tactics_Basic.run_safe uu____3469 ps1  in
                           let uu____3472 =
                             let uu____3473 =
                               FStar_Tactics_Embedding.e_result er  in
                             let uu____3478 =
                               FStar_TypeChecker_Cfg.psc_range psc  in
                             FStar_Syntax_Embeddings.embed uu____3473
                               uu____3478 r
                              in
                           FStar_Pervasives_Native.Some uu____3472)
  
let mk_tactic_interpretation_5 :
  'a 'b 'c 'd 'e 'r .
    ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'c FStar_Syntax_Embeddings.embedding ->
            'd FStar_Syntax_Embeddings.embedding ->
              'e FStar_Syntax_Embeddings.embedding ->
                'r FStar_Syntax_Embeddings.embedding ->
                  FStar_TypeChecker_Cfg.psc ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun ee  ->
              fun er  ->
                fun psc  ->
                  fun args  ->
                    let uu____3617 =
                      extract_6 ea eb ec ed ee
                        FStar_Tactics_Embedding.e_proofstate args
                       in
                    FStar_Util.bind_opt uu____3617
                      (fun uu____3654  ->
                         match uu____3654 with
                         | (a,b,c,d,e,ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let r =
                               let uu____3679 = t a b c d e  in
                               FStar_Tactics_Basic.run_safe uu____3679 ps1
                                in
                             let uu____3682 =
                               let uu____3683 =
                                 FStar_Tactics_Embedding.e_result er  in
                               let uu____3688 =
                                 FStar_TypeChecker_Cfg.psc_range psc  in
                               FStar_Syntax_Embeddings.embed uu____3683
                                 uu____3688 r
                                in
                             FStar_Pervasives_Native.Some uu____3682)
  
let mk_tactic_interpretation_6 :
  'a 'b 'c 'd 'e 'f 'r .
    ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'c FStar_Syntax_Embeddings.embedding ->
            'd FStar_Syntax_Embeddings.embedding ->
              'e FStar_Syntax_Embeddings.embedding ->
                'f FStar_Syntax_Embeddings.embedding ->
                  'r FStar_Syntax_Embeddings.embedding ->
                    FStar_TypeChecker_Cfg.psc ->
                      FStar_Syntax_Syntax.args ->
                        FStar_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun ee  ->
              fun ef  ->
                fun er  ->
                  fun psc  ->
                    fun args  ->
                      let uu____3846 =
                        extract_7 ea eb ec ed ee ef
                          FStar_Tactics_Embedding.e_proofstate args
                         in
                      FStar_Util.bind_opt uu____3846
                        (fun uu____3888  ->
                           match uu____3888 with
                           | (a,b,c,d,e,f,ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let r =
                                 let uu____3916 = t a b c d e f  in
                                 FStar_Tactics_Basic.run_safe uu____3916 ps1
                                  in
                               let uu____3919 =
                                 let uu____3920 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____3925 =
                                   FStar_TypeChecker_Cfg.psc_range psc  in
                                 FStar_Syntax_Embeddings.embed uu____3920
                                   uu____3925 r
                                  in
                               FStar_Pervasives_Native.Some uu____3919)
  
let mk_tactic_nbe_interpretation_1 :
  'a 'r .
    ('a -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'r FStar_TypeChecker_NBETerm.embedding ->
          FStar_TypeChecker_NBETerm.args ->
            FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun er  ->
        fun args  ->
          let uu____3981 =
            extract_2_nbe ea FStar_Tactics_Embedding.e_proofstate_nbe args
             in
          FStar_Util.bind_opt uu____3981
            (fun uu____3997  ->
               match uu____3997 with
               | (a,ps) ->
                   let r =
                     let uu____4009 = t a  in
                     FStar_Tactics_Basic.run_safe uu____4009 ps  in
                   let uu____4012 =
                     let uu____4013 = FStar_Tactics_Embedding.e_result_nbe er
                        in
                     FStar_TypeChecker_NBETerm.embed uu____4013 r  in
                   FStar_Pervasives_Native.Some uu____4012)
  
let mk_tactic_nbe_interpretation_2 :
  'a 'b 'r .
    ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun er  ->
          fun args  ->
            let uu____4092 =
              extract_3_nbe ea eb FStar_Tactics_Embedding.e_proofstate_nbe
                args
               in
            FStar_Util.bind_opt uu____4092
              (fun uu____4113  ->
                 match uu____4113 with
                 | (a,b,ps) ->
                     let r =
                       let uu____4128 = t a b  in
                       FStar_Tactics_Basic.run_safe uu____4128 ps  in
                     let uu____4131 =
                       let uu____4132 =
                         FStar_Tactics_Embedding.e_result_nbe er  in
                       FStar_TypeChecker_NBETerm.embed uu____4132 r  in
                     FStar_Pervasives_Native.Some uu____4131)
  
let mk_tactic_nbe_interpretation_3 :
  'a 'b 'c 'r .
    ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'r FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.args ->
                FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun er  ->
            fun args  ->
              let uu____4230 =
                extract_4_nbe ea eb ec
                  FStar_Tactics_Embedding.e_proofstate_nbe args
                 in
              FStar_Util.bind_opt uu____4230
                (fun uu____4256  ->
                   match uu____4256 with
                   | (a,b,c,ps) ->
                       let r =
                         let uu____4274 = t a b c  in
                         FStar_Tactics_Basic.run_safe uu____4274 ps  in
                       let uu____4277 =
                         let uu____4278 =
                           FStar_Tactics_Embedding.e_result_nbe er  in
                         FStar_TypeChecker_NBETerm.embed uu____4278 r  in
                       FStar_Pervasives_Native.Some uu____4277)
  
let mk_tactic_nbe_interpretation_4 :
  'a 'b 'c 'd 'r .
    ('a -> 'b -> 'c -> 'd -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              'r FStar_TypeChecker_NBETerm.embedding ->
                FStar_TypeChecker_NBETerm.args ->
                  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun er  ->
              fun args  ->
                let uu____4395 =
                  extract_5_nbe ea eb ec ed
                    FStar_Tactics_Embedding.e_proofstate_nbe args
                   in
                FStar_Util.bind_opt uu____4395
                  (fun uu____4426  ->
                     match uu____4426 with
                     | (a,b,c,d,ps) ->
                         let r =
                           let uu____4447 = t a b c d  in
                           FStar_Tactics_Basic.run_safe uu____4447 ps  in
                         let uu____4450 =
                           let uu____4451 =
                             FStar_Tactics_Embedding.e_result_nbe er  in
                           FStar_TypeChecker_NBETerm.embed uu____4451 r  in
                         FStar_Pervasives_Native.Some uu____4450)
  
let mk_tactic_nbe_interpretation_5 :
  'a 'b 'c 'd 'e 'r .
    ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              'e FStar_TypeChecker_NBETerm.embedding ->
                'r FStar_TypeChecker_NBETerm.embedding ->
                  FStar_TypeChecker_NBETerm.args ->
                    FStar_TypeChecker_NBETerm.t
                      FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun ee  ->
              fun er  ->
                fun args  ->
                  let uu____4587 =
                    extract_6_nbe ea eb ec ed ee
                      FStar_Tactics_Embedding.e_proofstate_nbe args
                     in
                  FStar_Util.bind_opt uu____4587
                    (fun uu____4623  ->
                       match uu____4623 with
                       | (a,b,c,d,e,ps) ->
                           let r =
                             let uu____4647 = t a b c d e  in
                             FStar_Tactics_Basic.run_safe uu____4647 ps  in
                           let uu____4650 =
                             let uu____4651 =
                               FStar_Tactics_Embedding.e_result_nbe er  in
                             FStar_TypeChecker_NBETerm.embed uu____4651 r  in
                           FStar_Pervasives_Native.Some uu____4650)
  
let mk_tactic_nbe_interpretation_6 :
  'a 'b 'c 'd 'e 'f 'r .
    ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              'e FStar_TypeChecker_NBETerm.embedding ->
                'f FStar_TypeChecker_NBETerm.embedding ->
                  'r FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_NBETerm.args ->
                      FStar_TypeChecker_NBETerm.t
                        FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun ee  ->
              fun ef  ->
                fun er  ->
                  fun args  ->
                    let uu____4806 =
                      extract_7_nbe ea eb ec ed ee ef
                        FStar_Tactics_Embedding.e_proofstate_nbe args
                       in
                    FStar_Util.bind_opt uu____4806
                      (fun uu____4847  ->
                         match uu____4847 with
                         | (a,b,c,d,e,f,ps) ->
                             let r =
                               let uu____4874 = t a b c d e f  in
                               FStar_Tactics_Basic.run_safe uu____4874 ps  in
                             let uu____4877 =
                               let uu____4878 =
                                 FStar_Tactics_Embedding.e_result_nbe er  in
                               FStar_TypeChecker_NBETerm.embed uu____4878 r
                                in
                             FStar_Pervasives_Native.Some uu____4877)
  
let (step_from_native_step :
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Cfg.primitive_step)
  =
  fun s  ->
    {
      FStar_TypeChecker_Cfg.name = (s.FStar_Tactics_Native.name);
      FStar_TypeChecker_Cfg.arity = (s.FStar_Tactics_Native.arity);
      FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0");
      FStar_TypeChecker_Cfg.auto_reflect =
        (FStar_Pervasives_Native.Some
           (s.FStar_Tactics_Native.arity - (Prims.parse_int "1")));
      FStar_TypeChecker_Cfg.strong_reduction_ok =
        (s.FStar_Tactics_Native.strong_reduction_ok);
      FStar_TypeChecker_Cfg.requires_binder_substitution = false;
      FStar_TypeChecker_Cfg.interpretation = (s.FStar_Tactics_Native.tactic);
      FStar_TypeChecker_Cfg.interpretation_nbe =
        (FStar_TypeChecker_NBETerm.dummy_interp s.FStar_Tactics_Native.name)
    }
  
let (mk :
  Prims.string ->
    Prims.int ->
      Prims.int ->
        (FStar_TypeChecker_Cfg.psc ->
           FStar_Syntax_Syntax.args ->
             FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
          ->
          (FStar_TypeChecker_NBETerm.args ->
             FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
            -> FStar_TypeChecker_Cfg.primitive_step)
  =
  fun nm  ->
    fun arity  ->
      fun nunivs  ->
        fun interp  ->
          fun nbe_interp  ->
            let nm1 =
              FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]  in
            {
              FStar_TypeChecker_Cfg.name = nm1;
              FStar_TypeChecker_Cfg.arity = arity;
              FStar_TypeChecker_Cfg.univ_arity = nunivs;
              FStar_TypeChecker_Cfg.auto_reflect =
                (FStar_Pervasives_Native.Some (arity - (Prims.parse_int "1")));
              FStar_TypeChecker_Cfg.strong_reduction_ok = true;
              FStar_TypeChecker_Cfg.requires_binder_substitution = true;
              FStar_TypeChecker_Cfg.interpretation = interp;
              FStar_TypeChecker_Cfg.interpretation_nbe = nbe_interp
            }
  
let (native_tactics : FStar_Tactics_Native.native_primitive_step Prims.list)
  = FStar_Tactics_Native.list_all () 
let (native_tactics_steps : FStar_TypeChecker_Cfg.primitive_step Prims.list)
  = FStar_List.map step_from_native_step native_tactics 
let mktac1 :
  'a 'na 'nr 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              ('na -> 'nr FStar_Tactics_Basic.tac) ->
                'na FStar_TypeChecker_NBETerm.embedding ->
                  'nr FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun er  ->
            fun nf  ->
              fun nea  ->
                fun ner  ->
                  mk name (Prims.parse_int "2") nunivs
                    (mk_tactic_interpretation_1 f ea er)
                    (mk_tactic_nbe_interpretation_1 nf nea ner)
  
let mktac2 :
  'a 'b 'na 'nb 'nr 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                ('na -> 'nb -> 'nr FStar_Tactics_Basic.tac) ->
                  'na FStar_TypeChecker_NBETerm.embedding ->
                    'nb FStar_TypeChecker_NBETerm.embedding ->
                      'nr FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun er  ->
              fun nf  ->
                fun nea  ->
                  fun neb  ->
                    fun ner  ->
                      mk name (Prims.parse_int "3") nunivs
                        (mk_tactic_interpretation_2 f ea eb er)
                        (mk_tactic_nbe_interpretation_2 nf nea neb ner)
  
let mktac3 :
  'a 'b 'c 'na 'nb 'nc 'nr 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'c FStar_Syntax_Embeddings.embedding ->
                'r FStar_Syntax_Embeddings.embedding ->
                  ('na -> 'nb -> 'nc -> 'nr FStar_Tactics_Basic.tac) ->
                    'na FStar_TypeChecker_NBETerm.embedding ->
                      'nb FStar_TypeChecker_NBETerm.embedding ->
                        'nc FStar_TypeChecker_NBETerm.embedding ->
                          'nr FStar_TypeChecker_NBETerm.embedding ->
                            FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun ec  ->
              fun er  ->
                fun nf  ->
                  fun nea  ->
                    fun neb  ->
                      fun nec  ->
                        fun ner  ->
                          mk name (Prims.parse_int "4") nunivs
                            (mk_tactic_interpretation_3 f ea eb ec er)
                            (mk_tactic_nbe_interpretation_3 nf nea neb nec
                               ner)
  
let mktac4 :
  'a 'b 'c 'd 'na 'nb 'nc 'nd 'nr 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'c -> 'd -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'c FStar_Syntax_Embeddings.embedding ->
                'd FStar_Syntax_Embeddings.embedding ->
                  'r FStar_Syntax_Embeddings.embedding ->
                    ('na -> 'nb -> 'nc -> 'nd -> 'nr FStar_Tactics_Basic.tac)
                      ->
                      'na FStar_TypeChecker_NBETerm.embedding ->
                        'nb FStar_TypeChecker_NBETerm.embedding ->
                          'nc FStar_TypeChecker_NBETerm.embedding ->
                            'nd FStar_TypeChecker_NBETerm.embedding ->
                              'nr FStar_TypeChecker_NBETerm.embedding ->
                                FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun ec  ->
              fun ed  ->
                fun er  ->
                  fun nf  ->
                    fun nea  ->
                      fun neb  ->
                        fun nec  ->
                          fun ned  ->
                            fun ner  ->
                              mk name (Prims.parse_int "5") nunivs
                                (mk_tactic_interpretation_4 f ea eb ec ed er)
                                (mk_tactic_nbe_interpretation_4 nf nea neb
                                   nec ned ner)
  
let mktac5 :
  'a 'b 'c 'd 'e 'na 'nb 'nc 'nd 'ne 'nr 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'c FStar_Syntax_Embeddings.embedding ->
                'd FStar_Syntax_Embeddings.embedding ->
                  'e FStar_Syntax_Embeddings.embedding ->
                    'r FStar_Syntax_Embeddings.embedding ->
                      ('na ->
                         'nb ->
                           'nc -> 'nd -> 'ne -> 'nr FStar_Tactics_Basic.tac)
                        ->
                        'na FStar_TypeChecker_NBETerm.embedding ->
                          'nb FStar_TypeChecker_NBETerm.embedding ->
                            'nc FStar_TypeChecker_NBETerm.embedding ->
                              'nd FStar_TypeChecker_NBETerm.embedding ->
                                'ne FStar_TypeChecker_NBETerm.embedding ->
                                  'nr FStar_TypeChecker_NBETerm.embedding ->
                                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun ec  ->
              fun ed  ->
                fun ee  ->
                  fun er  ->
                    fun nf  ->
                      fun nea  ->
                        fun neb  ->
                          fun nec  ->
                            fun ned  ->
                              fun nee  ->
                                fun ner  ->
                                  mk name (Prims.parse_int "6") nunivs
                                    (mk_tactic_interpretation_5 f ea eb ec ed
                                       ee er)
                                    (mk_tactic_nbe_interpretation_5 nf nea
                                       neb nec ned nee ner)
  
let (mkt :
  Prims.string ->
    Prims.int ->
      Prims.int ->
        (FStar_TypeChecker_Cfg.psc ->
           FStar_Syntax_Syntax.args ->
             FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
          ->
          (FStar_TypeChecker_NBETerm.args ->
             FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
            -> FStar_TypeChecker_Cfg.primitive_step)
  =
  fun nm  ->
    fun arity  ->
      fun nunivs  ->
        fun interp  ->
          fun nbe_interp  ->
            let nm1 =
              FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]  in
            {
              FStar_TypeChecker_Cfg.name = nm1;
              FStar_TypeChecker_Cfg.arity = arity;
              FStar_TypeChecker_Cfg.univ_arity = nunivs;
              FStar_TypeChecker_Cfg.auto_reflect =
                FStar_Pervasives_Native.None;
              FStar_TypeChecker_Cfg.strong_reduction_ok = true;
              FStar_TypeChecker_Cfg.requires_binder_substitution = false;
              FStar_TypeChecker_Cfg.interpretation = interp;
              FStar_TypeChecker_Cfg.interpretation_nbe = nbe_interp
            }
  
let mk_total_interpretation_1 :
  'a 'r .
    ('a -> 'r) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'r FStar_Syntax_Embeddings.embedding ->
          FStar_TypeChecker_Cfg.psc ->
            FStar_Syntax_Syntax.args ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun ea  ->
      fun er  ->
        fun psc  ->
          fun args  ->
            let uu____5938 = extract_1 ea args  in
            FStar_Util.bind_opt uu____5938
              (fun a  ->
                 let r = f a  in
                 let uu____5946 =
                   let uu____5947 = FStar_TypeChecker_Cfg.psc_range psc  in
                   FStar_Syntax_Embeddings.embed er uu____5947 r  in
                 FStar_Pervasives_Native.Some uu____5946)
  
let mk_total_interpretation_2 :
  'a 'b 'r .
    ('a -> 'b -> 'r) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_TypeChecker_Cfg.psc ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun ea  ->
      fun eb  ->
        fun er  ->
          fun psc  ->
            fun args  ->
              let uu____6023 = extract_2 ea eb args  in
              FStar_Util.bind_opt uu____6023
                (fun uu____6039  ->
                   match uu____6039 with
                   | (a,b) ->
                       let r = f a b  in
                       let uu____6049 =
                         let uu____6050 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         FStar_Syntax_Embeddings.embed er uu____6050 r  in
                       FStar_Pervasives_Native.Some uu____6049)
  
let mk_total_nbe_interpretation_1 :
  'a 'r .
    ('a -> 'r) ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'r FStar_TypeChecker_NBETerm.embedding ->
          FStar_TypeChecker_NBETerm.args ->
            FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun f  ->
    fun ea  ->
      fun er  ->
        fun args  ->
          let uu____6100 = extract_1_nbe ea args  in
          FStar_Util.bind_opt uu____6100
            (fun a  ->
               let r = f a  in
               let uu____6108 = FStar_TypeChecker_NBETerm.embed er r  in
               FStar_Pervasives_Native.Some uu____6108)
  
let mk_total_nbe_interpretation_2 :
  'a 'b 'r .
    ('a -> 'b -> 'r) ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun f  ->
    fun ea  ->
      fun eb  ->
        fun er  ->
          fun args  ->
            let uu____6177 = extract_2_nbe ea eb args  in
            FStar_Util.bind_opt uu____6177
              (fun uu____6193  ->
                 match uu____6193 with
                 | (a,b) ->
                     let r = f a b  in
                     let uu____6203 = FStar_TypeChecker_NBETerm.embed er r
                        in
                     FStar_Pervasives_Native.Some uu____6203)
  
let mktot1 :
  'a 'na 'nr 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'r) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              ('na -> 'nr) ->
                'na FStar_TypeChecker_NBETerm.embedding ->
                  'nr FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun er  ->
            fun nf  ->
              fun nea  ->
                fun ner  ->
                  mkt name (Prims.parse_int "1") nunivs
                    (mk_total_interpretation_1 f ea er)
                    (mk_total_nbe_interpretation_1 nf nea ner)
  
let mktot2 :
  'a 'b 'na 'nb 'nr 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'r) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                ('na -> 'nb -> 'nr) ->
                  'na FStar_TypeChecker_NBETerm.embedding ->
                    'nb FStar_TypeChecker_NBETerm.embedding ->
                      'nr FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun er  ->
              fun nf  ->
                fun nea  ->
                  fun neb  ->
                    fun ner  ->
                      mkt name (Prims.parse_int "2") nunivs
                        (mk_total_interpretation_2 f ea eb er)
                        (mk_total_nbe_interpretation_2 nf nea neb ner)
  