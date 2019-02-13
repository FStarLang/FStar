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
  'Auu____60 .
    'Auu____60 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____60 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun rng  ->
      fun t  ->
        fun n1  ->
          let uu____89 = FStar_Syntax_Embeddings.embed e t  in
          uu____89 rng FStar_Pervasives_Native.None n1
  
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
        | (a,uu____159)::[] ->
            let uu____184 = unembed ea a ncb  in
            FStar_Util.bind_opt uu____184
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____191 -> failwith "extract_1: wrong number of arguments"
  
let extract_2 :
  'a 'b .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Embeddings.norm_cb ->
          FStar_Syntax_Syntax.args ->
            ('a,'b) FStar_Pervasives_Native_Tuple2.tuple2
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ncb  ->
        fun args  ->
          match args with
          | (a,uu____249)::(b,uu____251)::[] ->
              let uu____292 = unembed ea a ncb  in
              FStar_Util.bind_opt uu____292
                (fun a1  ->
                   let uu____304 = unembed eb b ncb  in
                   FStar_Util.bind_opt uu____304
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____319 -> failwith "extract_2: wrong number of arguments"
  
let extract_3 :
  'a 'b 'c .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          FStar_Syntax_Embeddings.norm_cb ->
            FStar_Syntax_Syntax.args ->
              ('a,'b,'c) FStar_Pervasives_Native_Tuple3.tuple3
                FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ncb  ->
          fun args  ->
            match args with
            | (a,uu____397)::(b,uu____399)::(c,uu____401)::[] ->
                let uu____458 = unembed ea a ncb  in
                FStar_Util.bind_opt uu____458
                  (fun a1  ->
                     let uu____472 = unembed eb b ncb  in
                     FStar_Util.bind_opt uu____472
                       (fun b1  ->
                          let uu____486 = unembed ec c ncb  in
                          FStar_Util.bind_opt uu____486
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____505 -> failwith "extract_3: wrong number of arguments"
  
let extract_4 :
  'a 'b 'c 'd .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            FStar_Syntax_Embeddings.norm_cb ->
              FStar_Syntax_Syntax.args ->
                ('a,'b,'c,'d) FStar_Pervasives_Native_Tuple4.tuple4
                  FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ncb  ->
            fun args  ->
              match args with
              | (a,uu____601)::(b,uu____603)::(c,uu____605)::(d,uu____607)::[]
                  ->
                  let uu____680 = unembed ea a ncb  in
                  FStar_Util.bind_opt uu____680
                    (fun a1  ->
                       let uu____696 = unembed eb b ncb  in
                       FStar_Util.bind_opt uu____696
                         (fun b1  ->
                            let uu____712 = unembed ec c ncb  in
                            FStar_Util.bind_opt uu____712
                              (fun c1  ->
                                 let uu____728 = unembed ed d ncb  in
                                 FStar_Util.bind_opt uu____728
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____751 -> failwith "extract_4: wrong number of arguments"
  
let extract_5 :
  'a 'b 'c 'd 'e .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            'e FStar_Syntax_Embeddings.embedding ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  ('a,'b,'c,'d,'e) FStar_Pervasives_Native_Tuple5.tuple5
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
                | (a,uu____865)::(b,uu____867)::(c,uu____869)::(d,uu____871)::
                    (e,uu____873)::[] ->
                    let uu____962 = unembed ea a ncb  in
                    FStar_Util.bind_opt uu____962
                      (fun a1  ->
                         let uu____980 = unembed eb b ncb  in
                         FStar_Util.bind_opt uu____980
                           (fun b1  ->
                              let uu____998 = unembed ec c ncb  in
                              FStar_Util.bind_opt uu____998
                                (fun c1  ->
                                   let uu____1016 = unembed ed d ncb  in
                                   FStar_Util.bind_opt uu____1016
                                     (fun d1  ->
                                        let uu____1034 = unembed ee e ncb  in
                                        FStar_Util.bind_opt uu____1034
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____1061 ->
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
                    ('a,'b,'c,'d,'e,'f) FStar_Pervasives_Native_Tuple6.tuple6
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
                  | (a,uu____1193)::(b,uu____1195)::(c,uu____1197)::(d,uu____1199)::
                      (e,uu____1201)::(f,uu____1203)::[] ->
                      let uu____1308 = unembed ea a ncb  in
                      FStar_Util.bind_opt uu____1308
                        (fun a1  ->
                           let uu____1328 = unembed eb b ncb  in
                           FStar_Util.bind_opt uu____1328
                             (fun b1  ->
                                let uu____1348 = unembed ec c ncb  in
                                FStar_Util.bind_opt uu____1348
                                  (fun c1  ->
                                     let uu____1368 = unembed ed d ncb  in
                                     FStar_Util.bind_opt uu____1368
                                       (fun d1  ->
                                          let uu____1388 = unembed ee e ncb
                                             in
                                          FStar_Util.bind_opt uu____1388
                                            (fun e1  ->
                                               let uu____1408 =
                                                 unembed ef f ncb  in
                                               FStar_Util.bind_opt uu____1408
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____1439 ->
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
                      ('a,'b,'c,'d,'e,'f,'g)
                        FStar_Pervasives_Native_Tuple7.tuple7
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
                    | (a,uu____1589)::(b,uu____1591)::(c,uu____1593)::
                        (d,uu____1595)::(e,uu____1597)::(f,uu____1599)::
                        (g,uu____1601)::[] ->
                        let uu____1722 = unembed ea a ncb  in
                        FStar_Util.bind_opt uu____1722
                          (fun a1  ->
                             let uu____1744 = unembed eb b ncb  in
                             FStar_Util.bind_opt uu____1744
                               (fun b1  ->
                                  let uu____1766 = unembed ec c ncb  in
                                  FStar_Util.bind_opt uu____1766
                                    (fun c1  ->
                                       let uu____1788 = unembed ed d ncb  in
                                       FStar_Util.bind_opt uu____1788
                                         (fun d1  ->
                                            let uu____1810 = unembed ee e ncb
                                               in
                                            FStar_Util.bind_opt uu____1810
                                              (fun e1  ->
                                                 let uu____1832 =
                                                   unembed ef f ncb  in
                                                 FStar_Util.bind_opt
                                                   uu____1832
                                                   (fun f1  ->
                                                      let uu____1854 =
                                                        unembed eg g ncb  in
                                                      FStar_Util.bind_opt
                                                        uu____1854
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____1889 ->
                        failwith "extract_7: wrong number of arguments"
  
let extract_14 :
  't1 't10 't11 't12 't13 't14 't2 't3 't4 't5 't6 't7 't8 't9 .
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
                              't14 FStar_Syntax_Embeddings.embedding ->
                                FStar_Syntax_Embeddings.norm_cb ->
                                  FStar_Syntax_Syntax.args ->
                                    ('t1,'t2,'t3,'t4,'t5,'t6,'t7,'t8,
                                      't9,'t10,'t11,'t12,'t13,'t14)
                                      FStar_Pervasives_Native_Tuple14.tuple14
                                      FStar_Pervasives_Native.option
  =
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
                            fun e_t14  ->
                              fun ncb  ->
                                fun args  ->
                                  match args with
                                  | (a1,uu____2153)::(a2,uu____2155)::
                                      (a3,uu____2157)::(a4,uu____2159)::
                                      (a5,uu____2161)::(a6,uu____2163)::
                                      (a7,uu____2165)::(a8,uu____2167)::
                                      (a9,uu____2169)::(a10,uu____2171)::
                                      (a11,uu____2173)::(a12,uu____2175)::
                                      (a13,uu____2177)::(a14,uu____2179)::[]
                                      ->
                                      let uu____2412 = unembed e_t1 a1 ncb
                                         in
                                      FStar_Util.bind_opt uu____2412
                                        (fun a15  ->
                                           let uu____2448 =
                                             unembed e_t2 a2 ncb  in
                                           FStar_Util.bind_opt uu____2448
                                             (fun a21  ->
                                                let uu____2484 =
                                                  unembed e_t3 a3 ncb  in
                                                FStar_Util.bind_opt
                                                  uu____2484
                                                  (fun a31  ->
                                                     let uu____2520 =
                                                       unembed e_t4 a4 ncb
                                                        in
                                                     FStar_Util.bind_opt
                                                       uu____2520
                                                       (fun a41  ->
                                                          let uu____2556 =
                                                            unembed e_t5 a5
                                                              ncb
                                                             in
                                                          FStar_Util.bind_opt
                                                            uu____2556
                                                            (fun a51  ->
                                                               let uu____2592
                                                                 =
                                                                 unembed e_t6
                                                                   a6 ncb
                                                                  in
                                                               FStar_Util.bind_opt
                                                                 uu____2592
                                                                 (fun a61  ->
                                                                    let uu____2628
                                                                    =
                                                                    unembed
                                                                    e_t7 a7
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2628
                                                                    (fun a71 
                                                                    ->
                                                                    let uu____2664
                                                                    =
                                                                    unembed
                                                                    e_t8 a8
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2664
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____2700
                                                                    =
                                                                    unembed
                                                                    e_t9 a9
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2700
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____2736
                                                                    =
                                                                    unembed
                                                                    e_t10 a10
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2736
                                                                    (fun a101
                                                                     ->
                                                                    let uu____2772
                                                                    =
                                                                    unembed
                                                                    e_t11 a11
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2772
                                                                    (fun a111
                                                                     ->
                                                                    let uu____2808
                                                                    =
                                                                    unembed
                                                                    e_t12 a12
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2808
                                                                    (fun a121
                                                                     ->
                                                                    let uu____2844
                                                                    =
                                                                    unembed
                                                                    e_t13 a13
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2844
                                                                    (fun a131
                                                                     ->
                                                                    let uu____2880
                                                                    =
                                                                    unembed
                                                                    e_t14 a14
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____2880
                                                                    (fun a141
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (a15,
                                                                    a21, a31,
                                                                    a41, a51,
                                                                    a61, a71,
                                                                    a81, a91,
                                                                    a101,
                                                                    a111,
                                                                    a121,
                                                                    a131,
                                                                    a141)))))))))))))))
                                  | uu____2943 ->
                                      failwith
                                        "extract_14: wrong number of arguments"
  
let extract_1_nbe :
  'a .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.args -> 'a FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun args  ->
        match args with
        | (a,uu____3007)::[] ->
            let uu____3016 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
            FStar_Util.bind_opt uu____3016
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____3021 -> failwith "extract_1_nbe: wrong number of arguments"
  
let extract_2_nbe :
  'a 'b .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          FStar_TypeChecker_NBETerm.args ->
            ('a,'b) FStar_Pervasives_Native_Tuple2.tuple2
              FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun args  ->
          match args with
          | (a,uu____3075)::(b,uu____3077)::[] ->
              let uu____3090 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
              FStar_Util.bind_opt uu____3090
                (fun a1  ->
                   let uu____3100 = FStar_TypeChecker_NBETerm.unembed eb cb b
                      in
                   FStar_Util.bind_opt uu____3100
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____3113 -> failwith "extract_2_nbe: wrong number of arguments"
  
let extract_3_nbe :
  'a 'b 'c .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              ('a,'b,'c) FStar_Pervasives_Native_Tuple3.tuple3
                FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun args  ->
            match args with
            | (a,uu____3187)::(b,uu____3189)::(c,uu____3191)::[] ->
                let uu____3208 = FStar_TypeChecker_NBETerm.unembed ea cb a
                   in
                FStar_Util.bind_opt uu____3208
                  (fun a1  ->
                     let uu____3220 =
                       FStar_TypeChecker_NBETerm.unembed eb cb b  in
                     FStar_Util.bind_opt uu____3220
                       (fun b1  ->
                          let uu____3232 =
                            FStar_TypeChecker_NBETerm.unembed ec cb c  in
                          FStar_Util.bind_opt uu____3232
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____3249 ->
                failwith "extract_3_nbe: wrong number of arguments"
  
let extract_4_nbe :
  'a 'b 'c 'd .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.args ->
                ('a,'b,'c,'d) FStar_Pervasives_Native_Tuple4.tuple4
                  FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun args  ->
              match args with
              | (a,uu____3341)::(b,uu____3343)::(c,uu____3345)::(d,uu____3347)::[]
                  ->
                  let uu____3368 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____3368
                    (fun a1  ->
                       let uu____3382 =
                         FStar_TypeChecker_NBETerm.unembed eb cb b  in
                       FStar_Util.bind_opt uu____3382
                         (fun b1  ->
                            let uu____3396 =
                              FStar_TypeChecker_NBETerm.unembed ec cb c  in
                            FStar_Util.bind_opt uu____3396
                              (fun c1  ->
                                 let uu____3410 =
                                   FStar_TypeChecker_NBETerm.unembed ed cb d
                                    in
                                 FStar_Util.bind_opt uu____3410
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____3431 ->
                  failwith "extract_4_nbe: wrong number of arguments"
  
let extract_5_nbe :
  'a 'b 'c 'd 'e .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              'e FStar_TypeChecker_NBETerm.embedding ->
                FStar_TypeChecker_NBETerm.args ->
                  ('a,'b,'c,'d,'e) FStar_Pervasives_Native_Tuple5.tuple5
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
                | (a,uu____3541)::(b,uu____3543)::(c,uu____3545)::(d,uu____3547)::
                    (e,uu____3549)::[] ->
                    let uu____3574 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____3574
                      (fun a1  ->
                         let uu____3590 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____3590
                           (fun b1  ->
                              let uu____3606 =
                                FStar_TypeChecker_NBETerm.unembed ec cb c  in
                              FStar_Util.bind_opt uu____3606
                                (fun c1  ->
                                   let uu____3622 =
                                     FStar_TypeChecker_NBETerm.unembed ed cb
                                       d
                                      in
                                   FStar_Util.bind_opt uu____3622
                                     (fun d1  ->
                                        let uu____3638 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            ee cb e
                                           in
                                        FStar_Util.bind_opt uu____3638
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____3663 ->
                    failwith "extract_5_nbe: wrong number of arguments"
  
let extract_6_nbe :
  'a 'b 'c 'd 'e 'f .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              'e FStar_TypeChecker_NBETerm.embedding ->
                'f FStar_TypeChecker_NBETerm.embedding ->
                  FStar_TypeChecker_NBETerm.args ->
                    ('a,'b,'c,'d,'e,'f) FStar_Pervasives_Native_Tuple6.tuple6
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
                  | (a,uu____3791)::(b,uu____3793)::(c,uu____3795)::(d,uu____3797)::
                      (e,uu____3799)::(f,uu____3801)::[] ->
                      let uu____3830 =
                        FStar_TypeChecker_NBETerm.unembed ea cb a  in
                      FStar_Util.bind_opt uu____3830
                        (fun a1  ->
                           let uu____3848 =
                             FStar_TypeChecker_NBETerm.unembed eb cb b  in
                           FStar_Util.bind_opt uu____3848
                             (fun b1  ->
                                let uu____3866 =
                                  FStar_TypeChecker_NBETerm.unembed ec cb c
                                   in
                                FStar_Util.bind_opt uu____3866
                                  (fun c1  ->
                                     let uu____3884 =
                                       FStar_TypeChecker_NBETerm.unembed ed
                                         cb d
                                        in
                                     FStar_Util.bind_opt uu____3884
                                       (fun d1  ->
                                          let uu____3902 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              ee cb e
                                             in
                                          FStar_Util.bind_opt uu____3902
                                            (fun e1  ->
                                               let uu____3920 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   ef cb f
                                                  in
                                               FStar_Util.bind_opt uu____3920
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____3949 ->
                      failwith "extract_6_nbe: wrong number of arguments"
  
let extract_7_nbe :
  'a 'b 'c 'd 'e 'f 'g .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              'e FStar_TypeChecker_NBETerm.embedding ->
                'f FStar_TypeChecker_NBETerm.embedding ->
                  'g FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_NBETerm.args ->
                      ('a,'b,'c,'d,'e,'f,'g)
                        FStar_Pervasives_Native_Tuple7.tuple7
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
                    | (a,uu____4095)::(b,uu____4097)::(c,uu____4099)::
                        (d,uu____4101)::(e,uu____4103)::(f,uu____4105)::
                        (g,uu____4107)::[] ->
                        let uu____4140 =
                          FStar_TypeChecker_NBETerm.unembed ea cb a  in
                        FStar_Util.bind_opt uu____4140
                          (fun a1  ->
                             let uu____4160 =
                               FStar_TypeChecker_NBETerm.unembed eb cb b  in
                             FStar_Util.bind_opt uu____4160
                               (fun b1  ->
                                  let uu____4180 =
                                    FStar_TypeChecker_NBETerm.unembed ec cb c
                                     in
                                  FStar_Util.bind_opt uu____4180
                                    (fun c1  ->
                                       let uu____4200 =
                                         FStar_TypeChecker_NBETerm.unembed ed
                                           cb d
                                          in
                                       FStar_Util.bind_opt uu____4200
                                         (fun d1  ->
                                            let uu____4220 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                ee cb e
                                               in
                                            FStar_Util.bind_opt uu____4220
                                              (fun e1  ->
                                                 let uu____4240 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     ef cb f
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____4240
                                                   (fun f1  ->
                                                      let uu____4260 =
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          eg cb g
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____4260
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____4293 ->
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
              let uu____4383 =
                extract_2 ea FStar_Tactics_Embedding.e_proofstate ncb args
                 in
              FStar_Util.bind_opt uu____4383
                (fun uu____4402  ->
                   match uu____4402 with
                   | (a,ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let r =
                         let uu____4415 = t a  in
                         FStar_Tactics_Basic.run_safe uu____4415 ps1  in
                       let uu____4418 =
                         let uu____4419 = FStar_Tactics_Embedding.e_result er
                            in
                         let uu____4424 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         embed uu____4419 uu____4424 r ncb  in
                       FStar_Pervasives_Native.Some uu____4418)
  
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
                let uu____4520 =
                  extract_3 ea eb FStar_Tactics_Embedding.e_proofstate ncb
                    args
                   in
                FStar_Util.bind_opt uu____4520
                  (fun uu____4544  ->
                     match uu____4544 with
                     | (a,b,ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let r =
                           let uu____4560 = t a b  in
                           FStar_Tactics_Basic.run_safe uu____4560 ps1  in
                         let uu____4563 =
                           let uu____4564 =
                             FStar_Tactics_Embedding.e_result er  in
                           let uu____4569 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed uu____4564 uu____4569 r ncb  in
                         FStar_Pervasives_Native.Some uu____4563)
  
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
                  let uu____4684 =
                    extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                      ncb args
                     in
                  FStar_Util.bind_opt uu____4684
                    (fun uu____4713  ->
                       match uu____4713 with
                       | (a,b,c,ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let r =
                             let uu____4732 = t a b c  in
                             FStar_Tactics_Basic.run_safe uu____4732 ps1  in
                           let uu____4735 =
                             let uu____4736 =
                               FStar_Tactics_Embedding.e_result er  in
                             let uu____4741 =
                               FStar_TypeChecker_Cfg.psc_range psc  in
                             embed uu____4736 uu____4741 r ncb  in
                           FStar_Pervasives_Native.Some uu____4735)
  
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
                    let uu____4875 =
                      extract_5 ea eb ec ed
                        FStar_Tactics_Embedding.e_proofstate ncb args
                       in
                    FStar_Util.bind_opt uu____4875
                      (fun uu____4909  ->
                         match uu____4909 with
                         | (a,b,c,d,ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let r =
                               let uu____4931 = t a b c d  in
                               FStar_Tactics_Basic.run_safe uu____4931 ps1
                                in
                             let uu____4934 =
                               let uu____4935 =
                                 FStar_Tactics_Embedding.e_result er  in
                               let uu____4940 =
                                 FStar_TypeChecker_Cfg.psc_range psc  in
                               embed uu____4935 uu____4940 r ncb  in
                             FStar_Pervasives_Native.Some uu____4934)
  
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
                      let uu____5093 =
                        extract_6 ea eb ec ed ee
                          FStar_Tactics_Embedding.e_proofstate ncb args
                         in
                      FStar_Util.bind_opt uu____5093
                        (fun uu____5132  ->
                           match uu____5132 with
                           | (a,b,c,d,e,ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let r =
                                 let uu____5157 = t a b c d e  in
                                 FStar_Tactics_Basic.run_safe uu____5157 ps1
                                  in
                               let uu____5160 =
                                 let uu____5161 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____5166 =
                                   FStar_TypeChecker_Cfg.psc_range psc  in
                                 embed uu____5161 uu____5166 r ncb  in
                               FStar_Pervasives_Native.Some uu____5160)
  
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
                        let uu____5338 =
                          extract_7 ea eb ec ed ee ef
                            FStar_Tactics_Embedding.e_proofstate ncb args
                           in
                        FStar_Util.bind_opt uu____5338
                          (fun uu____5382  ->
                             match uu____5382 with
                             | (a,b,c,d,e,f,ps) ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 let r =
                                   let uu____5410 = t a b c d e f  in
                                   FStar_Tactics_Basic.run_safe uu____5410
                                     ps1
                                    in
                                 let uu____5413 =
                                   let uu____5414 =
                                     FStar_Tactics_Embedding.e_result er  in
                                   let uu____5419 =
                                     FStar_TypeChecker_Cfg.psc_range psc  in
                                   embed uu____5414 uu____5419 r ncb  in
                                 FStar_Pervasives_Native.Some uu____5413)
  
let mk_tactic_interpretation_13 :
  'r 't1 't10 't11 't12 't13 't2 't3 't4 't5 't6 't7 't8 't9 .
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
                                  FStar_TypeChecker_Cfg.psc ->
                                    FStar_Syntax_Embeddings.norm_cb ->
                                      FStar_Syntax_Syntax.args ->
                                        FStar_Syntax_Syntax.term
                                          FStar_Pervasives_Native.option
  =
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
                                fun psc  ->
                                  fun ncb  ->
                                    fun args  ->
                                      let uu____5724 =
                                        extract_14 e_t1 e_t2 e_t3 e_t4 e_t5
                                          e_t6 e_t7 e_t8 e_t9 e_t10 e_t11
                                          e_t12 e_t13
                                          FStar_Tactics_Embedding.e_proofstate
                                          ncb args
                                         in
                                      FStar_Util.bind_opt uu____5724
                                        (fun uu____5803  ->
                                           match uu____5803 with
                                           | (a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,ps)
                                               ->
                                               let ps1 =
                                                 FStar_Tactics_Types.set_ps_psc
                                                   psc ps
                                                  in
                                               let r =
                                                 let uu____5852 =
                                                   t a1 a2 a3 a4 a5 a6 a7 a8
                                                     a9 a10 a11 a12 a13
                                                    in
                                                 FStar_Tactics_Basic.run_safe
                                                   uu____5852 ps1
                                                  in
                                               let uu____5855 =
                                                 let uu____5856 =
                                                   FStar_Tactics_Embedding.e_result
                                                     er
                                                    in
                                                 let uu____5861 =
                                                   FStar_TypeChecker_Cfg.psc_range
                                                     psc
                                                    in
                                                 embed uu____5856 uu____5861
                                                   r ncb
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____5855)
  
let mk_tactic_nbe_interpretation_1 :
  'a 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
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
            let uu____5927 =
              extract_2_nbe cb ea FStar_Tactics_Embedding.e_proofstate_nbe
                args
               in
            FStar_Util.bind_opt uu____5927
              (fun uu____5943  ->
                 match uu____5943 with
                 | (a,ps) ->
                     let r =
                       let uu____5955 = t a  in
                       FStar_Tactics_Basic.run_safe uu____5955 ps  in
                     let uu____5958 =
                       let uu____5959 =
                         FStar_Tactics_Embedding.e_result_nbe er  in
                       FStar_TypeChecker_NBETerm.embed uu____5959 cb r  in
                     FStar_Pervasives_Native.Some uu____5958)
  
let mk_tactic_nbe_interpretation_2 :
  'a 'b 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
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
              let uu____6046 =
                extract_3_nbe cb ea eb
                  FStar_Tactics_Embedding.e_proofstate_nbe args
                 in
              FStar_Util.bind_opt uu____6046
                (fun uu____6067  ->
                   match uu____6067 with
                   | (a,b,ps) ->
                       let r =
                         let uu____6082 = t a b  in
                         FStar_Tactics_Basic.run_safe uu____6082 ps  in
                       let uu____6085 =
                         let uu____6086 =
                           FStar_Tactics_Embedding.e_result_nbe er  in
                         FStar_TypeChecker_NBETerm.embed uu____6086 cb r  in
                       FStar_Pervasives_Native.Some uu____6085)
  
let mk_tactic_nbe_interpretation_3 :
  'a 'b 'c 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
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
                let uu____6192 =
                  extract_4_nbe cb ea eb ec
                    FStar_Tactics_Embedding.e_proofstate_nbe args
                   in
                FStar_Util.bind_opt uu____6192
                  (fun uu____6218  ->
                     match uu____6218 with
                     | (a,b,c,ps) ->
                         let r =
                           let uu____6236 = t a b c  in
                           FStar_Tactics_Basic.run_safe uu____6236 ps  in
                         let uu____6239 =
                           let uu____6240 =
                             FStar_Tactics_Embedding.e_result_nbe er  in
                           FStar_TypeChecker_NBETerm.embed uu____6240 cb r
                            in
                         FStar_Pervasives_Native.Some uu____6239)
  
let mk_tactic_nbe_interpretation_4 :
  'a 'b 'c 'd 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
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
                  let uu____6365 =
                    extract_5_nbe cb ea eb ec ed
                      FStar_Tactics_Embedding.e_proofstate_nbe args
                     in
                  FStar_Util.bind_opt uu____6365
                    (fun uu____6396  ->
                       match uu____6396 with
                       | (a,b,c,d,ps) ->
                           let r =
                             let uu____6417 = t a b c d  in
                             FStar_Tactics_Basic.run_safe uu____6417 ps  in
                           let uu____6420 =
                             let uu____6421 =
                               FStar_Tactics_Embedding.e_result_nbe er  in
                             FStar_TypeChecker_NBETerm.embed uu____6421 cb r
                              in
                           FStar_Pervasives_Native.Some uu____6420)
  
let mk_tactic_nbe_interpretation_5 :
  'a 'b 'c 'd 'e 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
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
                    let uu____6565 =
                      extract_6_nbe cb ea eb ec ed ee
                        FStar_Tactics_Embedding.e_proofstate_nbe args
                       in
                    FStar_Util.bind_opt uu____6565
                      (fun uu____6601  ->
                         match uu____6601 with
                         | (a,b,c,d,e,ps) ->
                             let r =
                               let uu____6625 = t a b c d e  in
                               FStar_Tactics_Basic.run_safe uu____6625 ps  in
                             let uu____6628 =
                               let uu____6629 =
                                 FStar_Tactics_Embedding.e_result_nbe er  in
                               FStar_TypeChecker_NBETerm.embed uu____6629 cb
                                 r
                                in
                             FStar_Pervasives_Native.Some uu____6628)
  
let mk_tactic_nbe_interpretation_6 :
  'a 'b 'c 'd 'e 'f 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
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
                      let uu____6792 =
                        extract_7_nbe cb ea eb ec ed ee ef
                          FStar_Tactics_Embedding.e_proofstate_nbe args
                         in
                      FStar_Util.bind_opt uu____6792
                        (fun uu____6833  ->
                           match uu____6833 with
                           | (a,b,c,d,e,f,ps) ->
                               let r =
                                 let uu____6860 = t a b c d e f  in
                                 FStar_Tactics_Basic.run_safe uu____6860 ps
                                  in
                               let uu____6863 =
                                 let uu____6864 =
                                   FStar_Tactics_Embedding.e_result_nbe er
                                    in
                                 FStar_TypeChecker_NBETerm.embed uu____6864
                                   cb r
                                  in
                               FStar_Pervasives_Native.Some uu____6863)
  
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
  
let timing_int :
  'Auu____6902 'Auu____6903 'Auu____6904 'Auu____6905 .
    FStar_Ident.lid ->
      ('Auu____6902 -> 'Auu____6903 -> 'Auu____6904 -> 'Auu____6905) ->
        'Auu____6902 -> 'Auu____6903 -> 'Auu____6904 -> 'Auu____6905
  =
  fun l  ->
    fun f  -> fun psc  -> fun cb  -> fun args  -> let r = f psc cb args  in r
  
let timing_nbe :
  'Auu____6962 'Auu____6963 'Auu____6964 .
    FStar_Ident.lid ->
      ('Auu____6962 -> 'Auu____6963 -> 'Auu____6964) ->
        'Auu____6962 -> 'Auu____6963 -> 'Auu____6964
  =
  fun l  ->
    fun f  -> fun nbe_cbs  -> fun args  -> let r = f nbe_cbs args  in r
  
let (mk :
  Prims.string ->
    Prims.int ->
      Prims.int ->
        (FStar_TypeChecker_Cfg.psc ->
           FStar_Syntax_Embeddings.norm_cb ->
             FStar_Syntax_Syntax.args ->
               FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
          ->
          (FStar_TypeChecker_NBETerm.nbe_cbs ->
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
              FStar_TypeChecker_Cfg.interpretation = (timing_int nm1 interp);
              FStar_TypeChecker_Cfg.interpretation_nbe =
                (timing_nbe nm1 nbe_interp)
            }
  
let (native_tactics :
  unit -> FStar_Tactics_Native.native_primitive_step Prims.list) =
  fun uu____7086  -> FStar_Tactics_Native.list_all () 
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____7094  ->
    let uu____7095 = native_tactics ()  in
    FStar_List.map step_from_native_step uu____7095
  
let rec drop :
  'Auu____7105 .
    Prims.int -> 'Auu____7105 Prims.list -> 'Auu____7105 Prims.list
  =
  fun n1  ->
    fun l  ->
      if n1 = (Prims.parse_int "0")
      then l
      else
        (match l with
         | [] -> failwith "drop: impossible"
         | uu____7134::xs -> drop (n1 - (Prims.parse_int "1")) xs)
  
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
                         let uu____7252 = drop nunivs args  in
                         mk_tactic_nbe_interpretation_1 cb nf nea ner
                           uu____7252)
  
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
                             let uu____7408 = drop nunivs args  in
                             mk_tactic_nbe_interpretation_2 cb nf nea neb ner
                               uu____7408)
  
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
                                 let uu____7602 = drop nunivs args  in
                                 mk_tactic_nbe_interpretation_3 cb nf nea neb
                                   nec ner uu____7602)
  
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
                                     let uu____7834 = drop nunivs args  in
                                     mk_tactic_nbe_interpretation_4 cb nf nea
                                       neb nec ned ner uu____7834)
  
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
                                         let uu____8104 = drop nunivs args
                                            in
                                         mk_tactic_nbe_interpretation_5 cb nf
                                           nea neb nec ned nee ner uu____8104)
  
let (mkt :
  Prims.string ->
    Prims.int ->
      Prims.int ->
        (FStar_TypeChecker_Cfg.psc ->
           FStar_Syntax_Embeddings.norm_cb ->
             FStar_Syntax_Syntax.args ->
               FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
          ->
          (FStar_TypeChecker_NBETerm.nbe_cbs ->
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
              FStar_TypeChecker_Cfg.interpretation = (timing_int nm1 interp);
              FStar_TypeChecker_Cfg.interpretation_nbe =
                (timing_nbe nm1 nbe_interp)
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
              let uu____8259 = extract_1 ea ncb args  in
              FStar_Util.bind_opt uu____8259
                (fun a  ->
                   let r = f a  in
                   let uu____8269 =
                     let uu____8270 = FStar_TypeChecker_Cfg.psc_range psc  in
                     embed er uu____8270 r ncb  in
                   FStar_Pervasives_Native.Some uu____8269)
  
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
                let uu____8360 = extract_2 ea eb ncb args  in
                FStar_Util.bind_opt uu____8360
                  (fun uu____8378  ->
                     match uu____8378 with
                     | (a,b) ->
                         let r = f a b  in
                         let uu____8388 =
                           let uu____8389 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed er uu____8389 r ncb  in
                         FStar_Pervasives_Native.Some uu____8388)
  
let mk_total_nbe_interpretation_1 :
  'a 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
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
            let uu____8449 = extract_1_nbe cb ea args  in
            FStar_Util.bind_opt uu____8449
              (fun a  ->
                 let r = f a  in
                 let uu____8457 = FStar_TypeChecker_NBETerm.embed er cb r  in
                 FStar_Pervasives_Native.Some uu____8457)
  
let mk_total_nbe_interpretation_2 :
  'a 'b 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
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
              let uu____8534 = extract_2_nbe cb ea eb args  in
              FStar_Util.bind_opt uu____8534
                (fun uu____8550  ->
                   match uu____8550 with
                   | (a,b) ->
                       let r = f a b  in
                       let uu____8560 =
                         FStar_TypeChecker_NBETerm.embed er cb r  in
                       FStar_Pervasives_Native.Some uu____8560)
  
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
                         let uu____8666 = drop nunivs args  in
                         mk_total_nbe_interpretation_1 cb nf nea ner
                           uu____8666)
  
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
                             let uu____8814 = drop nunivs args  in
                             mk_total_nbe_interpretation_2 cb nf nea neb ner
                               uu____8814)
  