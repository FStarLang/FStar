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
    FStar_TypeChecker_NBETerm.iapp_cb ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.args -> 'a FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun args  ->
        match args with
        | (a,uu____1932)::[] ->
            let uu____1941 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
            FStar_Util.bind_opt uu____1941
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____1950 -> failwith "extract_1_nbe: wrong number of arguments"
  
let extract_2_nbe :
  'a 'b .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          FStar_TypeChecker_NBETerm.args ->
            ('a,'b) FStar_Pervasives_Native.tuple2
              FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun args  ->
          match args with
          | (a,uu____2012)::(b,uu____2014)::[] ->
              let uu____2027 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
              FStar_Util.bind_opt uu____2027
                (fun a1  ->
                   let uu____2041 = FStar_TypeChecker_NBETerm.unembed eb cb b
                      in
                   FStar_Util.bind_opt uu____2041
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____2058 -> failwith "extract_2_nbe: wrong number of arguments"
  
let extract_3_nbe :
  'a 'b 'c .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              ('a,'b,'c) FStar_Pervasives_Native.tuple3
                FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun args  ->
            match args with
            | (a,uu____2140)::(b,uu____2142)::(c,uu____2144)::[] ->
                let uu____2161 = FStar_TypeChecker_NBETerm.unembed ea cb a
                   in
                FStar_Util.bind_opt uu____2161
                  (fun a1  ->
                     let uu____2177 =
                       FStar_TypeChecker_NBETerm.unembed eb cb b  in
                     FStar_Util.bind_opt uu____2177
                       (fun b1  ->
                          let uu____2193 =
                            FStar_TypeChecker_NBETerm.unembed ec cb c  in
                          FStar_Util.bind_opt uu____2193
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____2214 ->
                failwith "extract_3_nbe: wrong number of arguments"
  
let extract_4_nbe :
  'a 'b 'c 'd .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.args ->
                ('a,'b,'c,'d) FStar_Pervasives_Native.tuple4
                  FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun args  ->
              match args with
              | (a,uu____2314)::(b,uu____2316)::(c,uu____2318)::(d,uu____2320)::[]
                  ->
                  let uu____2341 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____2341
                    (fun a1  ->
                       let uu____2359 =
                         FStar_TypeChecker_NBETerm.unembed eb cb b  in
                       FStar_Util.bind_opt uu____2359
                         (fun b1  ->
                            let uu____2377 =
                              FStar_TypeChecker_NBETerm.unembed ec cb c  in
                            FStar_Util.bind_opt uu____2377
                              (fun c1  ->
                                 let uu____2395 =
                                   FStar_TypeChecker_NBETerm.unembed ed cb d
                                    in
                                 FStar_Util.bind_opt uu____2395
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____2420 ->
                  failwith "extract_4_nbe: wrong number of arguments"
  
let extract_5_nbe :
  'a 'b 'c 'd 'e .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              'e FStar_TypeChecker_NBETerm.embedding ->
                FStar_TypeChecker_NBETerm.args ->
                  ('a,'b,'c,'d,'e) FStar_Pervasives_Native.tuple5
                    FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun ee  ->
              fun args  ->
                match args with
                | (a,uu____2538)::(b,uu____2540)::(c,uu____2542)::(d,uu____2544)::
                    (e,uu____2546)::[] ->
                    let uu____2571 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____2571
                      (fun a1  ->
                         let uu____2591 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____2591
                           (fun b1  ->
                              let uu____2611 =
                                FStar_TypeChecker_NBETerm.unembed ec cb c  in
                              FStar_Util.bind_opt uu____2611
                                (fun c1  ->
                                   let uu____2631 =
                                     FStar_TypeChecker_NBETerm.unembed ed cb
                                       d
                                      in
                                   FStar_Util.bind_opt uu____2631
                                     (fun d1  ->
                                        let uu____2651 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            ee cb e
                                           in
                                        FStar_Util.bind_opt uu____2651
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____2680 ->
                    failwith "extract_5_nbe: wrong number of arguments"
  
let extract_6_nbe :
  'a 'b 'c 'd 'e 'f .
    FStar_TypeChecker_NBETerm.iapp_cb ->
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
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun ee  ->
              fun ef  ->
                fun args  ->
                  match args with
                  | (a,uu____2816)::(b,uu____2818)::(c,uu____2820)::(d,uu____2822)::
                      (e,uu____2824)::(f,uu____2826)::[] ->
                      let uu____2855 =
                        FStar_TypeChecker_NBETerm.unembed ea cb a  in
                      FStar_Util.bind_opt uu____2855
                        (fun a1  ->
                           let uu____2877 =
                             FStar_TypeChecker_NBETerm.unembed eb cb b  in
                           FStar_Util.bind_opt uu____2877
                             (fun b1  ->
                                let uu____2899 =
                                  FStar_TypeChecker_NBETerm.unembed ec cb c
                                   in
                                FStar_Util.bind_opt uu____2899
                                  (fun c1  ->
                                     let uu____2921 =
                                       FStar_TypeChecker_NBETerm.unembed ed
                                         cb d
                                        in
                                     FStar_Util.bind_opt uu____2921
                                       (fun d1  ->
                                          let uu____2943 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              ee cb e
                                             in
                                          FStar_Util.bind_opt uu____2943
                                            (fun e1  ->
                                               let uu____2965 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   ef cb f
                                                  in
                                               FStar_Util.bind_opt uu____2965
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____2998 ->
                      failwith "extract_6_nbe: wrong number of arguments"
  
let extract_7_nbe :
  'a 'b 'c 'd 'e 'f 'g .
    FStar_TypeChecker_NBETerm.iapp_cb ->
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
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun ee  ->
              fun ef  ->
                fun eg  ->
                  fun args  ->
                    match args with
                    | (a,uu____3152)::(b,uu____3154)::(c,uu____3156)::
                        (d,uu____3158)::(e,uu____3160)::(f,uu____3162)::
                        (g,uu____3164)::[] ->
                        let uu____3197 =
                          FStar_TypeChecker_NBETerm.unembed ea cb a  in
                        FStar_Util.bind_opt uu____3197
                          (fun a1  ->
                             let uu____3221 =
                               FStar_TypeChecker_NBETerm.unembed eb cb b  in
                             FStar_Util.bind_opt uu____3221
                               (fun b1  ->
                                  let uu____3245 =
                                    FStar_TypeChecker_NBETerm.unembed ec cb c
                                     in
                                  FStar_Util.bind_opt uu____3245
                                    (fun c1  ->
                                       let uu____3269 =
                                         FStar_TypeChecker_NBETerm.unembed ed
                                           cb d
                                          in
                                       FStar_Util.bind_opt uu____3269
                                         (fun d1  ->
                                            let uu____3293 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                ee cb e
                                               in
                                            FStar_Util.bind_opt uu____3293
                                              (fun e1  ->
                                                 let uu____3317 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     ef cb f
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____3317
                                                   (fun f1  ->
                                                      let uu____3341 =
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          eg cb g
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____3341
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____3378 ->
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
              let uu____3466 =
                extract_2 ea FStar_Tactics_Embedding.e_proofstate ncb args
                 in
              FStar_Util.bind_opt uu____3466
                (fun uu____3485  ->
                   match uu____3485 with
                   | (a,ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let r =
                         let uu____3498 = t a  in
                         FStar_Tactics_Basic.run_safe uu____3498 ps1  in
                       let uu____3501 =
                         let uu____3502 = FStar_Tactics_Embedding.e_result er
                            in
                         let uu____3507 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         embed uu____3502 uu____3507 r ncb  in
                       FStar_Pervasives_Native.Some uu____3501)
  
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
                let uu____3602 =
                  extract_3 ea eb FStar_Tactics_Embedding.e_proofstate ncb
                    args
                   in
                FStar_Util.bind_opt uu____3602
                  (fun uu____3626  ->
                     match uu____3626 with
                     | (a,b,ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let r =
                           let uu____3642 = t a b  in
                           FStar_Tactics_Basic.run_safe uu____3642 ps1  in
                         let uu____3645 =
                           let uu____3646 =
                             FStar_Tactics_Embedding.e_result er  in
                           let uu____3651 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed uu____3646 uu____3651 r ncb  in
                         FStar_Pervasives_Native.Some uu____3645)
  
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
                  let uu____3765 =
                    extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                      ncb args
                     in
                  FStar_Util.bind_opt uu____3765
                    (fun uu____3794  ->
                       match uu____3794 with
                       | (a,b,c,ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let r =
                             let uu____3813 = t a b c  in
                             FStar_Tactics_Basic.run_safe uu____3813 ps1  in
                           let uu____3816 =
                             let uu____3817 =
                               FStar_Tactics_Embedding.e_result er  in
                             let uu____3822 =
                               FStar_TypeChecker_Cfg.psc_range psc  in
                             embed uu____3817 uu____3822 r ncb  in
                           FStar_Pervasives_Native.Some uu____3816)
  
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
                    let uu____3955 =
                      extract_5 ea eb ec ed
                        FStar_Tactics_Embedding.e_proofstate ncb args
                       in
                    FStar_Util.bind_opt uu____3955
                      (fun uu____3989  ->
                         match uu____3989 with
                         | (a,b,c,d,ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let r =
                               let uu____4011 = t a b c d  in
                               FStar_Tactics_Basic.run_safe uu____4011 ps1
                                in
                             let uu____4014 =
                               let uu____4015 =
                                 FStar_Tactics_Embedding.e_result er  in
                               let uu____4020 =
                                 FStar_TypeChecker_Cfg.psc_range psc  in
                               embed uu____4015 uu____4020 r ncb  in
                             FStar_Pervasives_Native.Some uu____4014)
  
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
                      let uu____4172 =
                        extract_6 ea eb ec ed ee
                          FStar_Tactics_Embedding.e_proofstate ncb args
                         in
                      FStar_Util.bind_opt uu____4172
                        (fun uu____4211  ->
                           match uu____4211 with
                           | (a,b,c,d,e,ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let r =
                                 let uu____4236 = t a b c d e  in
                                 FStar_Tactics_Basic.run_safe uu____4236 ps1
                                  in
                               let uu____4239 =
                                 let uu____4240 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____4245 =
                                   FStar_TypeChecker_Cfg.psc_range psc  in
                                 embed uu____4240 uu____4245 r ncb  in
                               FStar_Pervasives_Native.Some uu____4239)
  
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
                        let uu____4416 =
                          extract_7 ea eb ec ed ee ef
                            FStar_Tactics_Embedding.e_proofstate ncb args
                           in
                        FStar_Util.bind_opt uu____4416
                          (fun uu____4460  ->
                             match uu____4460 with
                             | (a,b,c,d,e,f,ps) ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 let r =
                                   let uu____4488 = t a b c d e f  in
                                   FStar_Tactics_Basic.run_safe uu____4488
                                     ps1
                                    in
                                 let uu____4491 =
                                   let uu____4492 =
                                     FStar_Tactics_Embedding.e_result er  in
                                   let uu____4497 =
                                     FStar_TypeChecker_Cfg.psc_range psc  in
                                   embed uu____4492 uu____4497 r ncb  in
                                 FStar_Pervasives_Native.Some uu____4491)
  
let mk_tactic_nbe_interpretation_1 :
  'a 'r .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      ('a -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun ea  ->
        fun er  ->
          fun args  ->
            let uu____4572 =
              extract_2_nbe cb ea FStar_Tactics_Embedding.e_proofstate_nbe
                args
               in
            FStar_Util.bind_opt uu____4572
              (fun uu____4592  ->
                 match uu____4592 with
                 | (a,ps) ->
                     let r =
                       let uu____4604 = t a  in
                       FStar_Tactics_Basic.run_safe uu____4604 ps  in
                     let uu____4607 =
                       let uu____4608 =
                         FStar_Tactics_Embedding.e_result_nbe er  in
                       FStar_TypeChecker_NBETerm.embed uu____4608 cb r  in
                     FStar_Pervasives_Native.Some uu____4607)
  
let mk_tactic_nbe_interpretation_2 :
  'a 'b 'r .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'b FStar_TypeChecker_NBETerm.embedding ->
            'r FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.args ->
                FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun args  ->
              let uu____4708 =
                extract_3_nbe cb ea eb
                  FStar_Tactics_Embedding.e_proofstate_nbe args
                 in
              FStar_Util.bind_opt uu____4708
                (fun uu____4733  ->
                   match uu____4733 with
                   | (a,b,ps) ->
                       let r =
                         let uu____4748 = t a b  in
                         FStar_Tactics_Basic.run_safe uu____4748 ps  in
                       let uu____4751 =
                         let uu____4752 =
                           FStar_Tactics_Embedding.e_result_nbe er  in
                         FStar_TypeChecker_NBETerm.embed uu____4752 cb r  in
                       FStar_Pervasives_Native.Some uu____4751)
  
let mk_tactic_nbe_interpretation_3 :
  'a 'b 'c 'r .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'b FStar_TypeChecker_NBETerm.embedding ->
            'c FStar_TypeChecker_NBETerm.embedding ->
              'r FStar_TypeChecker_NBETerm.embedding ->
                FStar_TypeChecker_NBETerm.args ->
                  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun er  ->
              fun args  ->
                let uu____4871 =
                  extract_4_nbe cb ea eb ec
                    FStar_Tactics_Embedding.e_proofstate_nbe args
                   in
                FStar_Util.bind_opt uu____4871
                  (fun uu____4901  ->
                     match uu____4901 with
                     | (a,b,c,ps) ->
                         let r =
                           let uu____4919 = t a b c  in
                           FStar_Tactics_Basic.run_safe uu____4919 ps  in
                         let uu____4922 =
                           let uu____4923 =
                             FStar_Tactics_Embedding.e_result_nbe er  in
                           FStar_TypeChecker_NBETerm.embed uu____4923 cb r
                            in
                         FStar_Pervasives_Native.Some uu____4922)
  
let mk_tactic_nbe_interpretation_4 :
  'a 'b 'c 'd 'r .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      ('a -> 'b -> 'c -> 'd -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'b FStar_TypeChecker_NBETerm.embedding ->
            'c FStar_TypeChecker_NBETerm.embedding ->
              'd FStar_TypeChecker_NBETerm.embedding ->
                'r FStar_TypeChecker_NBETerm.embedding ->
                  FStar_TypeChecker_NBETerm.args ->
                    FStar_TypeChecker_NBETerm.t
                      FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun ed  ->
              fun er  ->
                fun args  ->
                  let uu____5061 =
                    extract_5_nbe cb ea eb ec ed
                      FStar_Tactics_Embedding.e_proofstate_nbe args
                     in
                  FStar_Util.bind_opt uu____5061
                    (fun uu____5096  ->
                       match uu____5096 with
                       | (a,b,c,d,ps) ->
                           let r =
                             let uu____5117 = t a b c d  in
                             FStar_Tactics_Basic.run_safe uu____5117 ps  in
                           let uu____5120 =
                             let uu____5121 =
                               FStar_Tactics_Embedding.e_result_nbe er  in
                             FStar_TypeChecker_NBETerm.embed uu____5121 cb r
                              in
                           FStar_Pervasives_Native.Some uu____5120)
  
let mk_tactic_nbe_interpretation_5 :
  'a 'b 'c 'd 'e 'r .
    FStar_TypeChecker_NBETerm.iapp_cb ->
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
  fun cb  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun ed  ->
              fun ee  ->
                fun er  ->
                  fun args  ->
                    let uu____5278 =
                      extract_6_nbe cb ea eb ec ed ee
                        FStar_Tactics_Embedding.e_proofstate_nbe args
                       in
                    FStar_Util.bind_opt uu____5278
                      (fun uu____5318  ->
                         match uu____5318 with
                         | (a,b,c,d,e,ps) ->
                             let r =
                               let uu____5342 = t a b c d e  in
                               FStar_Tactics_Basic.run_safe uu____5342 ps  in
                             let uu____5345 =
                               let uu____5346 =
                                 FStar_Tactics_Embedding.e_result_nbe er  in
                               FStar_TypeChecker_NBETerm.embed uu____5346 cb
                                 r
                                in
                             FStar_Pervasives_Native.Some uu____5345)
  
let mk_tactic_nbe_interpretation_6 :
  'a 'b 'c 'd 'e 'f 'r .
    FStar_TypeChecker_NBETerm.iapp_cb ->
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
  fun cb  ->
    fun t  ->
      fun ea  ->
        fun eb  ->
          fun ec  ->
            fun ed  ->
              fun ee  ->
                fun ef  ->
                  fun er  ->
                    fun args  ->
                      let uu____5522 =
                        extract_7_nbe cb ea eb ec ed ee ef
                          FStar_Tactics_Embedding.e_proofstate_nbe args
                         in
                      FStar_Util.bind_opt uu____5522
                        (fun uu____5567  ->
                           match uu____5567 with
                           | (a,b,c,d,e,f,ps) ->
                               let r =
                                 let uu____5594 = t a b c d e f  in
                                 FStar_Tactics_Basic.run_safe uu____5594 ps
                                  in
                               let uu____5597 =
                                 let uu____5598 =
                                   FStar_Tactics_Embedding.e_result_nbe er
                                    in
                                 FStar_TypeChecker_NBETerm.embed uu____5598
                                   cb r
                                  in
                               FStar_Pervasives_Native.Some uu____5597)
  
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
        (fun _cb  ->
           FStar_TypeChecker_NBETerm.dummy_interp s.FStar_Tactics_Native.name)
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
          (FStar_TypeChecker_NBETerm.iapp_cb ->
             FStar_TypeChecker_NBETerm.args ->
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
  'Auu____5701 .
    Prims.int -> 'Auu____5701 Prims.list -> 'Auu____5701 Prims.list
  =
  fun n1  ->
    fun l  ->
      if n1 = (Prims.parse_int "0")
      then l
      else
        (match l with
         | [] -> failwith "drop: impossible"
         | uu____5723::xs -> drop (n1 - (Prims.parse_int "1")) xs)
  
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
                    (fun cb  ->
                       fun args  ->
                         let uu____5838 = drop nunivs args  in
                         mk_tactic_nbe_interpretation_1 cb nf nea ner
                           uu____5838)
  
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
                        (fun cb  ->
                           fun args  ->
                             let uu____5996 = drop nunivs args  in
                             mk_tactic_nbe_interpretation_2 cb nf nea neb ner
                               uu____5996)
  
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
                            (fun cb  ->
                               fun args  ->
                                 let uu____6192 = drop nunivs args  in
                                 mk_tactic_nbe_interpretation_3 cb nf nea neb
                                   nec ner uu____6192)
  
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
                                (fun cb  ->
                                   fun args  ->
                                     let uu____6426 = drop nunivs args  in
                                     mk_tactic_nbe_interpretation_4 cb nf nea
                                       neb nec ned ner uu____6426)
  
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
                                    (fun cb  ->
                                       fun args  ->
                                         let uu____6698 = drop nunivs args
                                            in
                                         mk_tactic_nbe_interpretation_5 cb nf
                                           nea neb nec ned nee ner uu____6698)
  
let (mkt :
  Prims.string ->
    Prims.int ->
      Prims.int ->
        (FStar_TypeChecker_Cfg.psc ->
           FStar_Syntax_Embeddings.norm_cb ->
             FStar_Syntax_Syntax.args ->
               FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
          ->
          (FStar_TypeChecker_NBETerm.iapp_cb ->
             FStar_TypeChecker_NBETerm.args ->
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
              let uu____6845 = extract_1 ea ncb args  in
              FStar_Util.bind_opt uu____6845
                (fun a  ->
                   let r = f a  in
                   let uu____6855 =
                     let uu____6856 = FStar_TypeChecker_Cfg.psc_range psc  in
                     embed er uu____6856 r ncb  in
                   FStar_Pervasives_Native.Some uu____6855)
  
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
                let uu____6945 = extract_2 ea eb ncb args  in
                FStar_Util.bind_opt uu____6945
                  (fun uu____6963  ->
                     match uu____6963 with
                     | (a,b) ->
                         let r = f a b  in
                         let uu____6973 =
                           let uu____6974 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed er uu____6974 r ncb  in
                         FStar_Pervasives_Native.Some uu____6973)
  
let mk_total_nbe_interpretation_1 :
  'a 'r .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      ('a -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          fun args  ->
            let uu____7043 = extract_1_nbe cb ea args  in
            FStar_Util.bind_opt uu____7043
              (fun a  ->
                 let r = f a  in
                 let uu____7055 = FStar_TypeChecker_NBETerm.embed er cb r  in
                 FStar_Pervasives_Native.Some uu____7055)
  
let mk_total_nbe_interpretation_2 :
  'a 'b 'r .
    FStar_TypeChecker_NBETerm.iapp_cb ->
      ('a -> 'b -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'b FStar_TypeChecker_NBETerm.embedding ->
            'r FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.args ->
                FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun args  ->
              let uu____7145 = extract_2_nbe cb ea eb args  in
              FStar_Util.bind_opt uu____7145
                (fun uu____7165  ->
                   match uu____7165 with
                   | (a,b) ->
                       let r = f a b  in
                       let uu____7175 =
                         FStar_TypeChecker_NBETerm.embed er cb r  in
                       FStar_Pervasives_Native.Some uu____7175)
  
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
                    (fun cb  ->
                       fun args  ->
                         let uu____7283 = drop nunivs args  in
                         mk_total_nbe_interpretation_1 cb nf nea ner
                           uu____7283)
  
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
                        (fun cb  ->
                           fun args  ->
                             let uu____7433 = drop nunivs args  in
                             mk_total_nbe_interpretation_2 cb nf nea neb ner
                               uu____7433)
  