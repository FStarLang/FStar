open Prims
let unembed :
  'Auu____9 .
    'Auu____9 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____9 FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  ->
        let uu____35 = FStar_Syntax_Embeddings.unembed e t  in
        uu____35 true n1
  
let embed :
  'Auu____58 .
    'Auu____58 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____58 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun rng  ->
      fun t  ->
        fun n1  ->
          let uu____87 = FStar_Syntax_Embeddings.embed e t  in
          uu____87 rng FStar_Pervasives_Native.None n1
  
let extract_1 :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Embeddings.norm_cb ->
        FStar_Syntax_Syntax.args -> 'a FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun ncb  ->
      fun args  ->
        match args with
        | (a,uu____156)::[] ->
            let uu____181 = unembed ea a ncb  in
            FStar_Util.bind_opt uu____181
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____188 -> failwith "extract_1: wrong number of arguments"
  
let extract_2 :
  'a 'b .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Embeddings.norm_cb ->
          FStar_Syntax_Syntax.args ->
            ('a,'b) FStar_Pervasives_Native.tuple2
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ncb  ->
        fun args  ->
          match args with
          | (a,uu____244)::(b,uu____246)::[] ->
              let uu____287 = unembed ea a ncb  in
              FStar_Util.bind_opt uu____287
                (fun a1  ->
                   let uu____299 = unembed eb b ncb  in
                   FStar_Util.bind_opt uu____299
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____314 -> failwith "extract_2: wrong number of arguments"
  
let extract_3 :
  'a 'b 'c .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          FStar_Syntax_Embeddings.norm_cb ->
            FStar_Syntax_Syntax.args ->
              ('a,'b,'c) FStar_Pervasives_Native.tuple3
                FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ncb  ->
          fun args  ->
            match args with
            | (a,uu____390)::(b,uu____392)::(c,uu____394)::[] ->
                let uu____451 = unembed ea a ncb  in
                FStar_Util.bind_opt uu____451
                  (fun a1  ->
                     let uu____465 = unembed eb b ncb  in
                     FStar_Util.bind_opt uu____465
                       (fun b1  ->
                          let uu____479 = unembed ec c ncb  in
                          FStar_Util.bind_opt uu____479
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____498 -> failwith "extract_3: wrong number of arguments"
  
let extract_4 :
  'a 'b 'c 'd .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            FStar_Syntax_Embeddings.norm_cb ->
              FStar_Syntax_Syntax.args ->
                ('a,'b,'c,'d) FStar_Pervasives_Native.tuple4
                  FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ncb  ->
            fun args  ->
              match args with
              | (a,uu____592)::(b,uu____594)::(c,uu____596)::(d,uu____598)::[]
                  ->
                  let uu____671 = unembed ea a ncb  in
                  FStar_Util.bind_opt uu____671
                    (fun a1  ->
                       let uu____687 = unembed eb b ncb  in
                       FStar_Util.bind_opt uu____687
                         (fun b1  ->
                            let uu____703 = unembed ec c ncb  in
                            FStar_Util.bind_opt uu____703
                              (fun c1  ->
                                 let uu____719 = unembed ed d ncb  in
                                 FStar_Util.bind_opt uu____719
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____742 -> failwith "extract_4: wrong number of arguments"
  
let extract_5 :
  'a 'b 'c 'd 'e .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            'e FStar_Syntax_Embeddings.embedding ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  ('a,'b,'c,'d,'e) FStar_Pervasives_Native.tuple5
                    FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ee  ->
            fun ncb  ->
              fun args  ->
                match args with
                | (a,uu____854)::(b,uu____856)::(c,uu____858)::(d,uu____860)::
                    (e,uu____862)::[] ->
                    let uu____951 = unembed ea a ncb  in
                    FStar_Util.bind_opt uu____951
                      (fun a1  ->
                         let uu____969 = unembed eb b ncb  in
                         FStar_Util.bind_opt uu____969
                           (fun b1  ->
                              let uu____987 = unembed ec c ncb  in
                              FStar_Util.bind_opt uu____987
                                (fun c1  ->
                                   let uu____1005 = unembed ed d ncb  in
                                   FStar_Util.bind_opt uu____1005
                                     (fun d1  ->
                                        let uu____1023 = unembed ee e ncb  in
                                        FStar_Util.bind_opt uu____1023
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____1050 ->
                    failwith "extract_5: wrong number of arguments"
  
let extract_6 :
  'a 'b 'c 'd 'e 'f .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            'e FStar_Syntax_Embeddings.embedding ->
              'f FStar_Syntax_Embeddings.embedding ->
                FStar_Syntax_Embeddings.norm_cb ->
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
              fun ncb  ->
                fun args  ->
                  match args with
                  | (a,uu____1180)::(b,uu____1182)::(c,uu____1184)::(d,uu____1186)::
                      (e,uu____1188)::(f,uu____1190)::[] ->
                      let uu____1295 = unembed ea a ncb  in
                      FStar_Util.bind_opt uu____1295
                        (fun a1  ->
                           let uu____1315 = unembed eb b ncb  in
                           FStar_Util.bind_opt uu____1315
                             (fun b1  ->
                                let uu____1335 = unembed ec c ncb  in
                                FStar_Util.bind_opt uu____1335
                                  (fun c1  ->
                                     let uu____1355 = unembed ed d ncb  in
                                     FStar_Util.bind_opt uu____1355
                                       (fun d1  ->
                                          let uu____1375 = unembed ee e ncb
                                             in
                                          FStar_Util.bind_opt uu____1375
                                            (fun e1  ->
                                               let uu____1395 =
                                                 unembed ef f ncb  in
                                               FStar_Util.bind_opt uu____1395
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____1426 ->
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
                  FStar_Syntax_Embeddings.norm_cb ->
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
                fun ncb  ->
                  fun args  ->
                    match args with
                    | (a,uu____1574)::(b,uu____1576)::(c,uu____1578)::
                        (d,uu____1580)::(e,uu____1582)::(f,uu____1584)::
                        (g,uu____1586)::[] ->
                        let uu____1707 = unembed ea a ncb  in
                        FStar_Util.bind_opt uu____1707
                          (fun a1  ->
                             let uu____1729 = unembed eb b ncb  in
                             FStar_Util.bind_opt uu____1729
                               (fun b1  ->
                                  let uu____1751 = unembed ec c ncb  in
                                  FStar_Util.bind_opt uu____1751
                                    (fun c1  ->
                                       let uu____1773 = unembed ed d ncb  in
                                       FStar_Util.bind_opt uu____1773
                                         (fun d1  ->
                                            let uu____1795 = unembed ee e ncb
                                               in
                                            FStar_Util.bind_opt uu____1795
                                              (fun e1  ->
                                                 let uu____1817 =
                                                   unembed ef f ncb  in
                                                 FStar_Util.bind_opt
                                                   uu____1817
                                                   (fun f1  ->
                                                      let uu____1839 =
                                                        unembed eg g ncb  in
                                                      FStar_Util.bind_opt
                                                        uu____1839
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____1874 ->
                        failwith "extract_7: wrong number of arguments"
  
let extract_1_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.args -> 'a FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun args  ->
      match args with
      | (a,uu____1915)::[] ->
          let uu____1924 = FStar_TypeChecker_NBETerm.unembed ea a  in
          FStar_Util.bind_opt uu____1924
            (fun a1  -> FStar_Pervasives_Native.Some a1)
      | uu____1929 -> failwith "extract_1_nbe: wrong number of arguments"
  
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
        | (a,uu____1974)::(b,uu____1976)::[] ->
            let uu____1989 = FStar_TypeChecker_NBETerm.unembed ea a  in
            FStar_Util.bind_opt uu____1989
              (fun a1  ->
                 let uu____1999 = FStar_TypeChecker_NBETerm.unembed eb b  in
                 FStar_Util.bind_opt uu____1999
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____2012 -> failwith "extract_2_nbe: wrong number of arguments"
  
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
          | (a,uu____2077)::(b,uu____2079)::(c,uu____2081)::[] ->
              let uu____2098 = FStar_TypeChecker_NBETerm.unembed ea a  in
              FStar_Util.bind_opt uu____2098
                (fun a1  ->
                   let uu____2110 = FStar_TypeChecker_NBETerm.unembed eb b
                      in
                   FStar_Util.bind_opt uu____2110
                     (fun b1  ->
                        let uu____2122 =
                          FStar_TypeChecker_NBETerm.unembed ec c  in
                        FStar_Util.bind_opt uu____2122
                          (fun c1  ->
                             FStar_Pervasives_Native.Some (a1, b1, c1))))
          | uu____2139 -> failwith "extract_3_nbe: wrong number of arguments"
  
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
            | (a,uu____2222)::(b,uu____2224)::(c,uu____2226)::(d,uu____2228)::[]
                ->
                let uu____2249 = FStar_TypeChecker_NBETerm.unembed ea a  in
                FStar_Util.bind_opt uu____2249
                  (fun a1  ->
                     let uu____2263 = FStar_TypeChecker_NBETerm.unembed eb b
                        in
                     FStar_Util.bind_opt uu____2263
                       (fun b1  ->
                          let uu____2277 =
                            FStar_TypeChecker_NBETerm.unembed ec c  in
                          FStar_Util.bind_opt uu____2277
                            (fun c1  ->
                               let uu____2291 =
                                 FStar_TypeChecker_NBETerm.unembed ed d  in
                               FStar_Util.bind_opt uu____2291
                                 (fun d1  ->
                                    FStar_Pervasives_Native.Some
                                      (a1, b1, c1, d1)))))
            | uu____2312 ->
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
              | (a,uu____2413)::(b,uu____2415)::(c,uu____2417)::(d,uu____2419)::
                  (e,uu____2421)::[] ->
                  let uu____2446 = FStar_TypeChecker_NBETerm.unembed ea a  in
                  FStar_Util.bind_opt uu____2446
                    (fun a1  ->
                       let uu____2462 =
                         FStar_TypeChecker_NBETerm.unembed eb b  in
                       FStar_Util.bind_opt uu____2462
                         (fun b1  ->
                            let uu____2478 =
                              FStar_TypeChecker_NBETerm.unembed ec c  in
                            FStar_Util.bind_opt uu____2478
                              (fun c1  ->
                                 let uu____2494 =
                                   FStar_TypeChecker_NBETerm.unembed ed d  in
                                 FStar_Util.bind_opt uu____2494
                                   (fun d1  ->
                                      let uu____2510 =
                                        FStar_TypeChecker_NBETerm.unembed ee
                                          e
                                         in
                                      FStar_Util.bind_opt uu____2510
                                        (fun e1  ->
                                           FStar_Pervasives_Native.Some
                                             (a1, b1, c1, d1, e1))))))
              | uu____2535 ->
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
                | (a,uu____2654)::(b,uu____2656)::(c,uu____2658)::(d,uu____2660)::
                    (e,uu____2662)::(f,uu____2664)::[] ->
                    let uu____2693 = FStar_TypeChecker_NBETerm.unembed ea a
                       in
                    FStar_Util.bind_opt uu____2693
                      (fun a1  ->
                         let uu____2711 =
                           FStar_TypeChecker_NBETerm.unembed eb b  in
                         FStar_Util.bind_opt uu____2711
                           (fun b1  ->
                              let uu____2729 =
                                FStar_TypeChecker_NBETerm.unembed ec c  in
                              FStar_Util.bind_opt uu____2729
                                (fun c1  ->
                                   let uu____2747 =
                                     FStar_TypeChecker_NBETerm.unembed ed d
                                      in
                                   FStar_Util.bind_opt uu____2747
                                     (fun d1  ->
                                        let uu____2765 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            ee e
                                           in
                                        FStar_Util.bind_opt uu____2765
                                          (fun e1  ->
                                             let uu____2783 =
                                               FStar_TypeChecker_NBETerm.unembed
                                                 ef f
                                                in
                                             FStar_Util.bind_opt uu____2783
                                               (fun f1  ->
                                                  FStar_Pervasives_Native.Some
                                                    (a1, b1, c1, d1, e1, f1)))))))
                | uu____2812 ->
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
                  | (a,uu____2949)::(b,uu____2951)::(c,uu____2953)::(d,uu____2955)::
                      (e,uu____2957)::(f,uu____2959)::(g,uu____2961)::[] ->
                      let uu____2994 = FStar_TypeChecker_NBETerm.unembed ea a
                         in
                      FStar_Util.bind_opt uu____2994
                        (fun a1  ->
                           let uu____3014 =
                             FStar_TypeChecker_NBETerm.unembed eb b  in
                           FStar_Util.bind_opt uu____3014
                             (fun b1  ->
                                let uu____3034 =
                                  FStar_TypeChecker_NBETerm.unembed ec c  in
                                FStar_Util.bind_opt uu____3034
                                  (fun c1  ->
                                     let uu____3054 =
                                       FStar_TypeChecker_NBETerm.unembed ed d
                                        in
                                     FStar_Util.bind_opt uu____3054
                                       (fun d1  ->
                                          let uu____3074 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              ee e
                                             in
                                          FStar_Util.bind_opt uu____3074
                                            (fun e1  ->
                                               let uu____3094 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   ef f
                                                  in
                                               FStar_Util.bind_opt uu____3094
                                                 (fun f1  ->
                                                    let uu____3114 =
                                                      FStar_TypeChecker_NBETerm.unembed
                                                        eg g
                                                       in
                                                    FStar_Util.bind_opt
                                                      uu____3114
                                                      (fun g1  ->
                                                         FStar_Pervasives_Native.Some
                                                           (a1, b1, c1, d1,
                                                             e1, f1, g1))))))))
                  | uu____3147 ->
                      failwith "extract_7_nbe: wrong number of arguments"
  
let mk_tactic_interpretation_1 :
  'a 'r .
    ('a -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'r FStar_Syntax_Embeddings.embedding ->
          FStar_TypeChecker_Cfg.psc ->
            FStar_Syntax_Embeddings.norm_cb ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun er  ->
        fun psc  ->
          fun ncb  ->
            fun args  ->
              let uu____3235 =
                extract_2 ea FStar_Tactics_Embedding.e_proofstate ncb args
                 in
              FStar_Util.bind_opt uu____3235
                (fun uu____3254  ->
                   match uu____3254 with
                   | (a,ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let r =
                         let uu____3267 = t a  in
                         FStar_Tactics_Basic.run_safe uu____3267 ps1  in
                       let uu____3270 =
                         let uu____3271 = FStar_Tactics_Embedding.e_result er
                            in
                         let uu____3276 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         embed uu____3271 uu____3276 r ncb  in
                       FStar_Pervasives_Native.Some uu____3270)
  
let mk_tactic_interpretation_2 :
  'a 'b 'r .
    ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_TypeChecker_Cfg.psc ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun er  ->
          fun psc  ->
            fun ncb  ->
              fun args  ->
                let uu____3371 =
                  extract_3 ea eb FStar_Tactics_Embedding.e_proofstate ncb
                    args
                   in
                FStar_Util.bind_opt uu____3371
                  (fun uu____3395  ->
                     match uu____3395 with
                     | (a,b,ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let r =
                           let uu____3411 = t a b  in
                           FStar_Tactics_Basic.run_safe uu____3411 ps1  in
                         let uu____3414 =
                           let uu____3415 =
                             FStar_Tactics_Embedding.e_result er  in
                           let uu____3420 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed uu____3415 uu____3420 r ncb  in
                         FStar_Pervasives_Native.Some uu____3414)
  
let mk_tactic_interpretation_3 :
  'a 'b 'c 'r .
    ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'c FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_TypeChecker_Cfg.psc ->
                FStar_Syntax_Embeddings.norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun er  ->
            fun psc  ->
              fun ncb  ->
                fun args  ->
                  let uu____3534 =
                    extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                      ncb args
                     in
                  FStar_Util.bind_opt uu____3534
                    (fun uu____3563  ->
                       match uu____3563 with
                       | (a,b,c,ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let r =
                             let uu____3582 = t a b c  in
                             FStar_Tactics_Basic.run_safe uu____3582 ps1  in
                           let uu____3585 =
                             let uu____3586 =
                               FStar_Tactics_Embedding.e_result er  in
                             let uu____3591 =
                               FStar_TypeChecker_Cfg.psc_range psc  in
                             embed uu____3586 uu____3591 r ncb  in
                           FStar_Pervasives_Native.Some uu____3585)
  
let mk_tactic_interpretation_4 :
  'a 'b 'c 'd 'r .
    ('a -> 'b -> 'c -> 'd -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'c FStar_Syntax_Embeddings.embedding ->
            'd FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                FStar_TypeChecker_Cfg.psc ->
                  FStar_Syntax_Embeddings.norm_cb ->
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
                fun ncb  ->
                  fun args  ->
                    let uu____3724 =
                      extract_5 ea eb ec ed
                        FStar_Tactics_Embedding.e_proofstate ncb args
                       in
                    FStar_Util.bind_opt uu____3724
                      (fun uu____3758  ->
                         match uu____3758 with
                         | (a,b,c,d,ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let r =
                               let uu____3780 = t a b c d  in
                               FStar_Tactics_Basic.run_safe uu____3780 ps1
                                in
                             let uu____3783 =
                               let uu____3784 =
                                 FStar_Tactics_Embedding.e_result er  in
                               let uu____3789 =
                                 FStar_TypeChecker_Cfg.psc_range psc  in
                               embed uu____3784 uu____3789 r ncb  in
                             FStar_Pervasives_Native.Some uu____3783)
  
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
                    FStar_Syntax_Embeddings.norm_cb ->
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
              fun er  ->
                fun psc  ->
                  fun ncb  ->
                    fun args  ->
                      let uu____3941 =
                        extract_6 ea eb ec ed ee
                          FStar_Tactics_Embedding.e_proofstate ncb args
                         in
                      FStar_Util.bind_opt uu____3941
                        (fun uu____3980  ->
                           match uu____3980 with
                           | (a,b,c,d,e,ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let r =
                                 let uu____4005 = t a b c d e  in
                                 FStar_Tactics_Basic.run_safe uu____4005 ps1
                                  in
                               let uu____4008 =
                                 let uu____4009 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____4014 =
                                   FStar_TypeChecker_Cfg.psc_range psc  in
                                 embed uu____4009 uu____4014 r ncb  in
                               FStar_Pervasives_Native.Some uu____4008)
  
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
                      FStar_Syntax_Embeddings.norm_cb ->
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
                    fun ncb  ->
                      fun args  ->
                        let uu____4185 =
                          extract_7 ea eb ec ed ee ef
                            FStar_Tactics_Embedding.e_proofstate ncb args
                           in
                        FStar_Util.bind_opt uu____4185
                          (fun uu____4229  ->
                             match uu____4229 with
                             | (a,b,c,d,e,f,ps) ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 let r =
                                   let uu____4257 = t a b c d e f  in
                                   FStar_Tactics_Basic.run_safe uu____4257
                                     ps1
                                    in
                                 let uu____4260 =
                                   let uu____4261 =
                                     FStar_Tactics_Embedding.e_result er  in
                                   let uu____4266 =
                                     FStar_TypeChecker_Cfg.psc_range psc  in
                                   embed uu____4261 uu____4266 r ncb  in
                                 FStar_Pervasives_Native.Some uu____4260)
  
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
          let uu____4324 =
            extract_2_nbe ea FStar_Tactics_Embedding.e_proofstate_nbe args
             in
          FStar_Util.bind_opt uu____4324
            (fun uu____4340  ->
               match uu____4340 with
               | (a,ps) ->
                   let r =
                     let uu____4352 = t a  in
                     FStar_Tactics_Basic.run_safe uu____4352 ps  in
                   let uu____4355 =
                     let uu____4356 = FStar_Tactics_Embedding.e_result_nbe er
                        in
                     FStar_TypeChecker_NBETerm.embed uu____4356 r  in
                   FStar_Pervasives_Native.Some uu____4355)
  
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
            let uu____4435 =
              extract_3_nbe ea eb FStar_Tactics_Embedding.e_proofstate_nbe
                args
               in
            FStar_Util.bind_opt uu____4435
              (fun uu____4456  ->
                 match uu____4456 with
                 | (a,b,ps) ->
                     let r =
                       let uu____4471 = t a b  in
                       FStar_Tactics_Basic.run_safe uu____4471 ps  in
                     let uu____4474 =
                       let uu____4475 =
                         FStar_Tactics_Embedding.e_result_nbe er  in
                       FStar_TypeChecker_NBETerm.embed uu____4475 r  in
                     FStar_Pervasives_Native.Some uu____4474)
  
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
              let uu____4573 =
                extract_4_nbe ea eb ec
                  FStar_Tactics_Embedding.e_proofstate_nbe args
                 in
              FStar_Util.bind_opt uu____4573
                (fun uu____4599  ->
                   match uu____4599 with
                   | (a,b,c,ps) ->
                       let r =
                         let uu____4617 = t a b c  in
                         FStar_Tactics_Basic.run_safe uu____4617 ps  in
                       let uu____4620 =
                         let uu____4621 =
                           FStar_Tactics_Embedding.e_result_nbe er  in
                         FStar_TypeChecker_NBETerm.embed uu____4621 r  in
                       FStar_Pervasives_Native.Some uu____4620)
  
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
                let uu____4738 =
                  extract_5_nbe ea eb ec ed
                    FStar_Tactics_Embedding.e_proofstate_nbe args
                   in
                FStar_Util.bind_opt uu____4738
                  (fun uu____4769  ->
                     match uu____4769 with
                     | (a,b,c,d,ps) ->
                         let r =
                           let uu____4790 = t a b c d  in
                           FStar_Tactics_Basic.run_safe uu____4790 ps  in
                         let uu____4793 =
                           let uu____4794 =
                             FStar_Tactics_Embedding.e_result_nbe er  in
                           FStar_TypeChecker_NBETerm.embed uu____4794 r  in
                         FStar_Pervasives_Native.Some uu____4793)
  
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
                  let uu____4930 =
                    extract_6_nbe ea eb ec ed ee
                      FStar_Tactics_Embedding.e_proofstate_nbe args
                     in
                  FStar_Util.bind_opt uu____4930
                    (fun uu____4966  ->
                       match uu____4966 with
                       | (a,b,c,d,e,ps) ->
                           let r =
                             let uu____4990 = t a b c d e  in
                             FStar_Tactics_Basic.run_safe uu____4990 ps  in
                           let uu____4993 =
                             let uu____4994 =
                               FStar_Tactics_Embedding.e_result_nbe er  in
                             FStar_TypeChecker_NBETerm.embed uu____4994 r  in
                           FStar_Pervasives_Native.Some uu____4993)
  
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
                    let uu____5149 =
                      extract_7_nbe ea eb ec ed ee ef
                        FStar_Tactics_Embedding.e_proofstate_nbe args
                       in
                    FStar_Util.bind_opt uu____5149
                      (fun uu____5190  ->
                         match uu____5190 with
                         | (a,b,c,d,e,f,ps) ->
                             let r =
                               let uu____5217 = t a b c d e f  in
                               FStar_Tactics_Basic.run_safe uu____5217 ps  in
                             let uu____5220 =
                               let uu____5221 =
                                 FStar_Tactics_Embedding.e_result_nbe er  in
                               FStar_TypeChecker_NBETerm.embed uu____5221 r
                                in
                             FStar_Pervasives_Native.Some uu____5220)
  
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
           FStar_Syntax_Embeddings.norm_cb ->
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
let rec drop :
  'Auu____5301 .
    Prims.int -> 'Auu____5301 Prims.list -> 'Auu____5301 Prims.list
  =
  fun n1  ->
    fun l  ->
      if n1 = (Prims.parse_int "0")
      then l
      else
        (match l with
         | [] -> failwith "drop: impossible"
         | uu____5323::xs -> drop (n1 - (Prims.parse_int "1")) xs)
  
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
                    (fun args  ->
                       let uu____5432 = drop nunivs args  in
                       mk_tactic_nbe_interpretation_1 nf nea ner uu____5432)
  
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
                        (fun args  ->
                           let uu____5580 = drop nunivs args  in
                           mk_tactic_nbe_interpretation_2 nf nea neb ner
                             uu____5580)
  
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
                            (fun args  ->
                               let uu____5766 = drop nunivs args  in
                               mk_tactic_nbe_interpretation_3 nf nea neb nec
                                 ner uu____5766)
  
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
                                (fun args  ->
                                   let uu____5990 = drop nunivs args  in
                                   mk_tactic_nbe_interpretation_4 nf nea neb
                                     nec ned ner uu____5990)
  
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
                                    (fun args  ->
                                       let uu____6252 = drop nunivs args  in
                                       mk_tactic_nbe_interpretation_5 nf nea
                                         neb nec ned nee ner uu____6252)
  
let (mkt :
  Prims.string ->
    Prims.int ->
      Prims.int ->
        (FStar_TypeChecker_Cfg.psc ->
           FStar_Syntax_Embeddings.norm_cb ->
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
            FStar_Syntax_Embeddings.norm_cb ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun ea  ->
      fun er  ->
        fun psc  ->
          fun ncb  ->
            fun args  ->
              let uu____6382 = extract_1 ea ncb args  in
              FStar_Util.bind_opt uu____6382
                (fun a  ->
                   let r = f a  in
                   let uu____6392 =
                     let uu____6393 = FStar_TypeChecker_Cfg.psc_range psc  in
                     embed er uu____6393 r ncb  in
                   FStar_Pervasives_Native.Some uu____6392)
  
let mk_total_interpretation_2 :
  'a 'b 'r .
    ('a -> 'b -> 'r) ->
      'a FStar_Syntax_Embeddings.embedding ->
        'b FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_TypeChecker_Cfg.psc ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun ea  ->
      fun eb  ->
        fun er  ->
          fun psc  ->
            fun ncb  ->
              fun args  ->
                let uu____6482 = extract_2 ea eb ncb args  in
                FStar_Util.bind_opt uu____6482
                  (fun uu____6500  ->
                     match uu____6500 with
                     | (a,b) ->
                         let r = f a b  in
                         let uu____6510 =
                           let uu____6511 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed er uu____6511 r ncb  in
                         FStar_Pervasives_Native.Some uu____6510)
  
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
          let uu____6563 = extract_1_nbe ea args  in
          FStar_Util.bind_opt uu____6563
            (fun a  ->
               let r = f a  in
               let uu____6571 = FStar_TypeChecker_NBETerm.embed er r  in
               FStar_Pervasives_Native.Some uu____6571)
  
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
            let uu____6640 = extract_2_nbe ea eb args  in
            FStar_Util.bind_opt uu____6640
              (fun uu____6656  ->
                 match uu____6656 with
                 | (a,b) ->
                     let r = f a b  in
                     let uu____6666 = FStar_TypeChecker_NBETerm.embed er r
                        in
                     FStar_Pervasives_Native.Some uu____6666)
  
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
                    (fun args  ->
                       let uu____6764 = drop nunivs args  in
                       mk_total_nbe_interpretation_1 nf nea ner uu____6764)
  
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
                        (fun args  ->
                           let uu____6904 = drop nunivs args  in
                           mk_total_nbe_interpretation_2 nf nea neb ner
                             uu____6904)
  