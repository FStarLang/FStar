open Prims
let unembed :
  'Auu____8 .
    'Auu____8 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____8 FStar_Pervasives_Native.option
  =
  fun e ->
    fun t ->
      fun n1 ->
        let uu____32 = FStar_Syntax_Embeddings.unembed e t in
        uu____32 true n1
let embed :
  'Auu____51 .
    'Auu____51 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____51 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun e ->
    fun rng ->
      fun t ->
        fun n1 ->
          let uu____78 = FStar_Syntax_Embeddings.embed e t in
          uu____78 rng FStar_Pervasives_Native.None n1
let extract_1 :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Embeddings.norm_cb ->
        FStar_Syntax_Syntax.args -> 'a FStar_Pervasives_Native.option
  =
  fun ea ->
    fun ncb ->
      fun args ->
        match args with
        | (a, uu____121)::[] ->
            let uu____146 = unembed ea a ncb in
            FStar_Util.bind_opt uu____146
              (fun a1 -> FStar_Pervasives_Native.Some a1)
        | uu____151 -> failwith "extract_1: wrong number of arguments"
let extract_2 :
  'a 'b .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Embeddings.norm_cb ->
          FStar_Syntax_Syntax.args ->
            ('a * 'b) FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ncb ->
        fun args ->
          match args with
          | (a, uu____207)::(b, uu____209)::[] ->
              let uu____250 = unembed ea a ncb in
              FStar_Util.bind_opt uu____250
                (fun a1 ->
                   let uu____260 = unembed eb b ncb in
                   FStar_Util.bind_opt uu____260
                     (fun b1 -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____273 -> failwith "extract_2: wrong number of arguments"
let extract_3 :
  'a 'b 'c .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          FStar_Syntax_Embeddings.norm_cb ->
            FStar_Syntax_Syntax.args ->
              ('a * 'b * 'c) FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ncb ->
          fun args ->
            match args with
            | (a, uu____349)::(b, uu____351)::(c, uu____353)::[] ->
                let uu____410 = unembed ea a ncb in
                FStar_Util.bind_opt uu____410
                  (fun a1 ->
                     let uu____422 = unembed eb b ncb in
                     FStar_Util.bind_opt uu____422
                       (fun b1 ->
                          let uu____434 = unembed ec c ncb in
                          FStar_Util.bind_opt uu____434
                            (fun c1 ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____451 -> failwith "extract_3: wrong number of arguments"
let extract_4 :
  'a 'b 'c 'd .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            FStar_Syntax_Embeddings.norm_cb ->
              FStar_Syntax_Syntax.args ->
                ('a * 'b * 'c * 'd) FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun ncb ->
            fun args ->
              match args with
              | (a, uu____545)::(b, uu____547)::(c, uu____549)::(d,
                                                                 uu____551)::[]
                  ->
                  let uu____624 = unembed ea a ncb in
                  FStar_Util.bind_opt uu____624
                    (fun a1 ->
                       let uu____638 = unembed eb b ncb in
                       FStar_Util.bind_opt uu____638
                         (fun b1 ->
                            let uu____652 = unembed ec c ncb in
                            FStar_Util.bind_opt uu____652
                              (fun c1 ->
                                 let uu____666 = unembed ed d ncb in
                                 FStar_Util.bind_opt uu____666
                                   (fun d1 ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____687 -> failwith "extract_4: wrong number of arguments"
let extract_5 :
  'a 'b 'c 'd 'e .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          'd FStar_Syntax_Embeddings.embedding ->
            'e FStar_Syntax_Embeddings.embedding ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  ('a * 'b * 'c * 'd * 'e) FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun ee ->
            fun ncb ->
              fun args ->
                match args with
                | (a, uu____799)::(b, uu____801)::(c, uu____803)::(d,
                                                                   uu____805)::
                    (e, uu____807)::[] ->
                    let uu____896 = unembed ea a ncb in
                    FStar_Util.bind_opt uu____896
                      (fun a1 ->
                         let uu____912 = unembed eb b ncb in
                         FStar_Util.bind_opt uu____912
                           (fun b1 ->
                              let uu____928 = unembed ec c ncb in
                              FStar_Util.bind_opt uu____928
                                (fun c1 ->
                                   let uu____944 = unembed ed d ncb in
                                   FStar_Util.bind_opt uu____944
                                     (fun d1 ->
                                        let uu____960 = unembed ee e ncb in
                                        FStar_Util.bind_opt uu____960
                                          (fun e1 ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____985 ->
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
                    ('a * 'b * 'c * 'd * 'e * 'f)
                      FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun ee ->
            fun ef ->
              fun ncb ->
                fun args ->
                  match args with
                  | (a, uu____1115)::(b, uu____1117)::(c, uu____1119)::
                      (d, uu____1121)::(e, uu____1123)::(f, uu____1125)::[]
                      ->
                      let uu____1230 = unembed ea a ncb in
                      FStar_Util.bind_opt uu____1230
                        (fun a1 ->
                           let uu____1248 = unembed eb b ncb in
                           FStar_Util.bind_opt uu____1248
                             (fun b1 ->
                                let uu____1266 = unembed ec c ncb in
                                FStar_Util.bind_opt uu____1266
                                  (fun c1 ->
                                     let uu____1284 = unembed ed d ncb in
                                     FStar_Util.bind_opt uu____1284
                                       (fun d1 ->
                                          let uu____1302 = unembed ee e ncb in
                                          FStar_Util.bind_opt uu____1302
                                            (fun e1 ->
                                               let uu____1320 =
                                                 unembed ef f ncb in
                                               FStar_Util.bind_opt uu____1320
                                                 (fun f1 ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____1349 ->
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
                      ('a * 'b * 'c * 'd * 'e * 'f * 'g)
                        FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun ee ->
            fun ef ->
              fun eg ->
                fun ncb ->
                  fun args ->
                    match args with
                    | (a, uu____1497)::(b, uu____1499)::(c, uu____1501)::
                        (d, uu____1503)::(e, uu____1505)::(f, uu____1507)::
                        (g, uu____1509)::[] ->
                        let uu____1630 = unembed ea a ncb in
                        FStar_Util.bind_opt uu____1630
                          (fun a1 ->
                             let uu____1650 = unembed eb b ncb in
                             FStar_Util.bind_opt uu____1650
                               (fun b1 ->
                                  let uu____1670 = unembed ec c ncb in
                                  FStar_Util.bind_opt uu____1670
                                    (fun c1 ->
                                       let uu____1690 = unembed ed d ncb in
                                       FStar_Util.bind_opt uu____1690
                                         (fun d1 ->
                                            let uu____1710 = unembed ee e ncb in
                                            FStar_Util.bind_opt uu____1710
                                              (fun e1 ->
                                                 let uu____1730 =
                                                   unembed ef f ncb in
                                                 FStar_Util.bind_opt
                                                   uu____1730
                                                   (fun f1 ->
                                                      let uu____1750 =
                                                        unembed eg g ncb in
                                                      FStar_Util.bind_opt
                                                        uu____1750
                                                        (fun g1 ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____1783 ->
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
                                    ('t1 * 't2 * 't3 * 't4 * 't5 * 't6 * 't7
                                      * 't8 * 't9 * 't10 * 't11 * 't12 * 't13
                                      * 't14) FStar_Pervasives_Native.option
  =
  fun e_t1 ->
    fun e_t2 ->
      fun e_t3 ->
        fun e_t4 ->
          fun e_t5 ->
            fun e_t6 ->
              fun e_t7 ->
                fun e_t8 ->
                  fun e_t9 ->
                    fun e_t10 ->
                      fun e_t11 ->
                        fun e_t12 ->
                          fun e_t13 ->
                            fun e_t14 ->
                              fun ncb ->
                                fun args ->
                                  match args with
                                  | (a1, uu____2045)::(a2, uu____2047)::
                                      (a3, uu____2049)::(a4, uu____2051)::
                                      (a5, uu____2053)::(a6, uu____2055)::
                                      (a7, uu____2057)::(a8, uu____2059)::
                                      (a9, uu____2061)::(a10, uu____2063)::
                                      (a11, uu____2065)::(a12, uu____2067)::
                                      (a13, uu____2069)::(a14, uu____2071)::[]
                                      ->
                                      let uu____2304 = unembed e_t1 a1 ncb in
                                      FStar_Util.bind_opt uu____2304
                                        (fun a15 ->
                                           let uu____2338 =
                                             unembed e_t2 a2 ncb in
                                           FStar_Util.bind_opt uu____2338
                                             (fun a21 ->
                                                let uu____2372 =
                                                  unembed e_t3 a3 ncb in
                                                FStar_Util.bind_opt
                                                  uu____2372
                                                  (fun a31 ->
                                                     let uu____2406 =
                                                       unembed e_t4 a4 ncb in
                                                     FStar_Util.bind_opt
                                                       uu____2406
                                                       (fun a41 ->
                                                          let uu____2440 =
                                                            unembed e_t5 a5
                                                              ncb in
                                                          FStar_Util.bind_opt
                                                            uu____2440
                                                            (fun a51 ->
                                                               let uu____2474
                                                                 =
                                                                 unembed e_t6
                                                                   a6 ncb in
                                                               FStar_Util.bind_opt
                                                                 uu____2474
                                                                 (fun a61 ->
                                                                    let uu____2508
                                                                    =
                                                                    unembed
                                                                    e_t7 a7
                                                                    ncb in
                                                                    FStar_Util.bind_opt
                                                                    uu____2508
                                                                    (fun a71
                                                                    ->
                                                                    let uu____2542
                                                                    =
                                                                    unembed
                                                                    e_t8 a8
                                                                    ncb in
                                                                    FStar_Util.bind_opt
                                                                    uu____2542
                                                                    (fun a81
                                                                    ->
                                                                    let uu____2576
                                                                    =
                                                                    unembed
                                                                    e_t9 a9
                                                                    ncb in
                                                                    FStar_Util.bind_opt
                                                                    uu____2576
                                                                    (fun a91
                                                                    ->
                                                                    let uu____2610
                                                                    =
                                                                    unembed
                                                                    e_t10 a10
                                                                    ncb in
                                                                    FStar_Util.bind_opt
                                                                    uu____2610
                                                                    (fun a101
                                                                    ->
                                                                    let uu____2644
                                                                    =
                                                                    unembed
                                                                    e_t11 a11
                                                                    ncb in
                                                                    FStar_Util.bind_opt
                                                                    uu____2644
                                                                    (fun a111
                                                                    ->
                                                                    let uu____2678
                                                                    =
                                                                    unembed
                                                                    e_t12 a12
                                                                    ncb in
                                                                    FStar_Util.bind_opt
                                                                    uu____2678
                                                                    (fun a121
                                                                    ->
                                                                    let uu____2712
                                                                    =
                                                                    unembed
                                                                    e_t13 a13
                                                                    ncb in
                                                                    FStar_Util.bind_opt
                                                                    uu____2712
                                                                    (fun a131
                                                                    ->
                                                                    let uu____2746
                                                                    =
                                                                    unembed
                                                                    e_t14 a14
                                                                    ncb in
                                                                    FStar_Util.bind_opt
                                                                    uu____2746
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
                                  | uu____2807 ->
                                      failwith
                                        "extract_14: wrong number of arguments"
let extract_1_nbe :
  'a .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.args -> 'a FStar_Pervasives_Native.option
  =
  fun cb ->
    fun ea ->
      fun args ->
        match args with
        | (a, uu____2871)::[] ->
            let uu____2880 = FStar_TypeChecker_NBETerm.unembed ea cb a in
            FStar_Util.bind_opt uu____2880
              (fun a1 -> FStar_Pervasives_Native.Some a1)
        | uu____2885 -> failwith "extract_1_nbe: wrong number of arguments"
let extract_2_nbe :
  'a 'b .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          FStar_TypeChecker_NBETerm.args ->
            ('a * 'b) FStar_Pervasives_Native.option
  =
  fun cb ->
    fun ea ->
      fun eb ->
        fun args ->
          match args with
          | (a, uu____2939)::(b, uu____2941)::[] ->
              let uu____2954 = FStar_TypeChecker_NBETerm.unembed ea cb a in
              FStar_Util.bind_opt uu____2954
                (fun a1 ->
                   let uu____2964 = FStar_TypeChecker_NBETerm.unembed eb cb b in
                   FStar_Util.bind_opt uu____2964
                     (fun b1 -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____2977 -> failwith "extract_2_nbe: wrong number of arguments"
let extract_3_nbe :
  'a 'b 'c .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              ('a * 'b * 'c) FStar_Pervasives_Native.option
  =
  fun cb ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun args ->
            match args with
            | (a, uu____3051)::(b, uu____3053)::(c, uu____3055)::[] ->
                let uu____3072 = FStar_TypeChecker_NBETerm.unembed ea cb a in
                FStar_Util.bind_opt uu____3072
                  (fun a1 ->
                     let uu____3084 =
                       FStar_TypeChecker_NBETerm.unembed eb cb b in
                     FStar_Util.bind_opt uu____3084
                       (fun b1 ->
                          let uu____3096 =
                            FStar_TypeChecker_NBETerm.unembed ec cb c in
                          FStar_Util.bind_opt uu____3096
                            (fun c1 ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____3113 ->
                failwith "extract_3_nbe: wrong number of arguments"
let extract_4_nbe :
  'a 'b 'c 'd .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            'd FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.args ->
                ('a * 'b * 'c * 'd) FStar_Pervasives_Native.option
  =
  fun cb ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun ed ->
            fun args ->
              match args with
              | (a, uu____3205)::(b, uu____3207)::(c, uu____3209)::(d,
                                                                    uu____3211)::[]
                  ->
                  let uu____3232 = FStar_TypeChecker_NBETerm.unembed ea cb a in
                  FStar_Util.bind_opt uu____3232
                    (fun a1 ->
                       let uu____3246 =
                         FStar_TypeChecker_NBETerm.unembed eb cb b in
                       FStar_Util.bind_opt uu____3246
                         (fun b1 ->
                            let uu____3260 =
                              FStar_TypeChecker_NBETerm.unembed ec cb c in
                            FStar_Util.bind_opt uu____3260
                              (fun c1 ->
                                 let uu____3274 =
                                   FStar_TypeChecker_NBETerm.unembed ed cb d in
                                 FStar_Util.bind_opt uu____3274
                                   (fun d1 ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____3295 ->
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
                  ('a * 'b * 'c * 'd * 'e) FStar_Pervasives_Native.option
  =
  fun cb ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun ed ->
            fun ee ->
              fun args ->
                match args with
                | (a, uu____3405)::(b, uu____3407)::(c, uu____3409)::
                    (d, uu____3411)::(e, uu____3413)::[] ->
                    let uu____3438 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a in
                    FStar_Util.bind_opt uu____3438
                      (fun a1 ->
                         let uu____3454 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b in
                         FStar_Util.bind_opt uu____3454
                           (fun b1 ->
                              let uu____3470 =
                                FStar_TypeChecker_NBETerm.unembed ec cb c in
                              FStar_Util.bind_opt uu____3470
                                (fun c1 ->
                                   let uu____3486 =
                                     FStar_TypeChecker_NBETerm.unembed ed cb
                                       d in
                                   FStar_Util.bind_opt uu____3486
                                     (fun d1 ->
                                        let uu____3502 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            ee cb e in
                                        FStar_Util.bind_opt uu____3502
                                          (fun e1 ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____3527 ->
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
                    ('a * 'b * 'c * 'd * 'e * 'f)
                      FStar_Pervasives_Native.option
  =
  fun cb ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun ed ->
            fun ee ->
              fun ef ->
                fun args ->
                  match args with
                  | (a, uu____3655)::(b, uu____3657)::(c, uu____3659)::
                      (d, uu____3661)::(e, uu____3663)::(f, uu____3665)::[]
                      ->
                      let uu____3694 =
                        FStar_TypeChecker_NBETerm.unembed ea cb a in
                      FStar_Util.bind_opt uu____3694
                        (fun a1 ->
                           let uu____3712 =
                             FStar_TypeChecker_NBETerm.unembed eb cb b in
                           FStar_Util.bind_opt uu____3712
                             (fun b1 ->
                                let uu____3730 =
                                  FStar_TypeChecker_NBETerm.unembed ec cb c in
                                FStar_Util.bind_opt uu____3730
                                  (fun c1 ->
                                     let uu____3748 =
                                       FStar_TypeChecker_NBETerm.unembed ed
                                         cb d in
                                     FStar_Util.bind_opt uu____3748
                                       (fun d1 ->
                                          let uu____3766 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              ee cb e in
                                          FStar_Util.bind_opt uu____3766
                                            (fun e1 ->
                                               let uu____3784 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   ef cb f in
                                               FStar_Util.bind_opt uu____3784
                                                 (fun f1 ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____3813 ->
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
                      ('a * 'b * 'c * 'd * 'e * 'f * 'g)
                        FStar_Pervasives_Native.option
  =
  fun cb ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun ed ->
            fun ee ->
              fun ef ->
                fun eg ->
                  fun args ->
                    match args with
                    | (a, uu____3959)::(b, uu____3961)::(c, uu____3963)::
                        (d, uu____3965)::(e, uu____3967)::(f, uu____3969)::
                        (g, uu____3971)::[] ->
                        let uu____4004 =
                          FStar_TypeChecker_NBETerm.unembed ea cb a in
                        FStar_Util.bind_opt uu____4004
                          (fun a1 ->
                             let uu____4024 =
                               FStar_TypeChecker_NBETerm.unembed eb cb b in
                             FStar_Util.bind_opt uu____4024
                               (fun b1 ->
                                  let uu____4044 =
                                    FStar_TypeChecker_NBETerm.unembed ec cb c in
                                  FStar_Util.bind_opt uu____4044
                                    (fun c1 ->
                                       let uu____4064 =
                                         FStar_TypeChecker_NBETerm.unembed ed
                                           cb d in
                                       FStar_Util.bind_opt uu____4064
                                         (fun d1 ->
                                            let uu____4084 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                ee cb e in
                                            FStar_Util.bind_opt uu____4084
                                              (fun e1 ->
                                                 let uu____4104 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     ef cb f in
                                                 FStar_Util.bind_opt
                                                   uu____4104
                                                   (fun f1 ->
                                                      let uu____4124 =
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          eg cb g in
                                                      FStar_Util.bind_opt
                                                        uu____4124
                                                        (fun g1 ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____4157 ->
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
  fun t ->
    fun ea ->
      fun er ->
        fun psc ->
          fun ncb ->
            fun args ->
              let uu____4245 =
                extract_2 ea FStar_Tactics_Embedding.e_proofstate ncb args in
              FStar_Util.bind_opt uu____4245
                (fun uu____4262 ->
                   match uu____4262 with
                   | (a, ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                       let r =
                         let uu____4275 = t a in
                         FStar_Tactics_Basic.run_safe uu____4275 ps1 in
                       let uu____4278 =
                         let uu____4279 = FStar_Tactics_Embedding.e_result er in
                         let uu____4284 = FStar_TypeChecker_Cfg.psc_range psc in
                         embed uu____4279 uu____4284 r ncb in
                       FStar_Pervasives_Native.Some uu____4278)
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
  fun t ->
    fun ea ->
      fun eb ->
        fun er ->
          fun psc ->
            fun ncb ->
              fun args ->
                let uu____4376 =
                  extract_3 ea eb FStar_Tactics_Embedding.e_proofstate ncb
                    args in
                FStar_Util.bind_opt uu____4376
                  (fun uu____4398 ->
                     match uu____4398 with
                     | (a, b, ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                         let r =
                           let uu____4414 = t a b in
                           FStar_Tactics_Basic.run_safe uu____4414 ps1 in
                         let uu____4417 =
                           let uu____4418 =
                             FStar_Tactics_Embedding.e_result er in
                           let uu____4423 =
                             FStar_TypeChecker_Cfg.psc_range psc in
                           embed uu____4418 uu____4423 r ncb in
                         FStar_Pervasives_Native.Some uu____4417)
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
  fun t ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun er ->
            fun psc ->
              fun ncb ->
                fun args ->
                  let uu____4534 =
                    extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                      ncb args in
                  FStar_Util.bind_opt uu____4534
                    (fun uu____4561 ->
                       match uu____4561 with
                       | (a, b, c, ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                           let r =
                             let uu____4580 = t a b c in
                             FStar_Tactics_Basic.run_safe uu____4580 ps1 in
                           let uu____4583 =
                             let uu____4584 =
                               FStar_Tactics_Embedding.e_result er in
                             let uu____4589 =
                               FStar_TypeChecker_Cfg.psc_range psc in
                             embed uu____4584 uu____4589 r ncb in
                           FStar_Pervasives_Native.Some uu____4583)
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
  fun t ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun ed ->
            fun er ->
              fun psc ->
                fun ncb ->
                  fun args ->
                    let uu____4719 =
                      extract_5 ea eb ec ed
                        FStar_Tactics_Embedding.e_proofstate ncb args in
                    FStar_Util.bind_opt uu____4719
                      (fun uu____4751 ->
                         match uu____4751 with
                         | (a, b, c, d, ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                             let r =
                               let uu____4773 = t a b c d in
                               FStar_Tactics_Basic.run_safe uu____4773 ps1 in
                             let uu____4776 =
                               let uu____4777 =
                                 FStar_Tactics_Embedding.e_result er in
                               let uu____4782 =
                                 FStar_TypeChecker_Cfg.psc_range psc in
                               embed uu____4777 uu____4782 r ncb in
                             FStar_Pervasives_Native.Some uu____4776)
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
  fun t ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun ed ->
            fun ee ->
              fun er ->
                fun psc ->
                  fun ncb ->
                    fun args ->
                      let uu____4931 =
                        extract_6 ea eb ec ed ee
                          FStar_Tactics_Embedding.e_proofstate ncb args in
                      FStar_Util.bind_opt uu____4931
                        (fun uu____4968 ->
                           match uu____4968 with
                           | (a, b, c, d, e, ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps in
                               let r =
                                 let uu____4993 = t a b c d e in
                                 FStar_Tactics_Basic.run_safe uu____4993 ps1 in
                               let uu____4996 =
                                 let uu____4997 =
                                   FStar_Tactics_Embedding.e_result er in
                                 let uu____5002 =
                                   FStar_TypeChecker_Cfg.psc_range psc in
                                 embed uu____4997 uu____5002 r ncb in
                               FStar_Pervasives_Native.Some uu____4996)
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
  fun t ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun ed ->
            fun ee ->
              fun ef ->
                fun er ->
                  fun psc ->
                    fun ncb ->
                      fun args ->
                        let uu____5170 =
                          extract_7 ea eb ec ed ee ef
                            FStar_Tactics_Embedding.e_proofstate ncb args in
                        FStar_Util.bind_opt uu____5170
                          (fun uu____5212 ->
                             match uu____5212 with
                             | (a, b, c, d, e, f, ps) ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps in
                                 let r =
                                   let uu____5240 = t a b c d e f in
                                   FStar_Tactics_Basic.run_safe uu____5240
                                     ps1 in
                                 let uu____5243 =
                                   let uu____5244 =
                                     FStar_Tactics_Embedding.e_result er in
                                   let uu____5249 =
                                     FStar_TypeChecker_Cfg.psc_range psc in
                                   embed uu____5244 uu____5249 r ncb in
                                 FStar_Pervasives_Native.Some uu____5243)
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
  fun t ->
    fun e_t1 ->
      fun e_t2 ->
        fun e_t3 ->
          fun e_t4 ->
            fun e_t5 ->
              fun e_t6 ->
                fun e_t7 ->
                  fun e_t8 ->
                    fun e_t9 ->
                      fun e_t10 ->
                        fun e_t11 ->
                          fun e_t12 ->
                            fun e_t13 ->
                              fun er ->
                                fun psc ->
                                  fun ncb ->
                                    fun args ->
                                      let uu____5550 =
                                        extract_14 e_t1 e_t2 e_t3 e_t4 e_t5
                                          e_t6 e_t7 e_t8 e_t9 e_t10 e_t11
                                          e_t12 e_t13
                                          FStar_Tactics_Embedding.e_proofstate
                                          ncb args in
                                      FStar_Util.bind_opt uu____5550
                                        (fun uu____5627 ->
                                           match uu____5627 with
                                           | (a1, a2, a3, a4, a5, a6, a7, a8,
                                              a9, a10, a11, a12, a13, ps) ->
                                               let ps1 =
                                                 FStar_Tactics_Types.set_ps_psc
                                                   psc ps in
                                               let r =
                                                 let uu____5676 =
                                                   t a1 a2 a3 a4 a5 a6 a7 a8
                                                     a9 a10 a11 a12 a13 in
                                                 FStar_Tactics_Basic.run_safe
                                                   uu____5676 ps1 in
                                               let uu____5679 =
                                                 let uu____5680 =
                                                   FStar_Tactics_Embedding.e_result
                                                     er in
                                                 let uu____5685 =
                                                   FStar_TypeChecker_Cfg.psc_range
                                                     psc in
                                                 embed uu____5680 uu____5685
                                                   r ncb in
                                               FStar_Pervasives_Native.Some
                                                 uu____5679)
let mk_tactic_nbe_interpretation_1 :
  'a 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('a -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb ->
    fun t ->
      fun ea ->
        fun er ->
          fun args ->
            let uu____5749 =
              extract_2_nbe cb ea FStar_Tactics_Embedding.e_proofstate_nbe
                args in
            FStar_Util.bind_opt uu____5749
              (fun uu____5765 ->
                 match uu____5765 with
                 | (a, ps) ->
                     let r =
                       let uu____5777 = t a in
                       FStar_Tactics_Basic.run_safe uu____5777 ps in
                     let uu____5780 =
                       let uu____5781 =
                         FStar_Tactics_Embedding.e_result_nbe er in
                       FStar_TypeChecker_NBETerm.embed uu____5781 cb r in
                     FStar_Pervasives_Native.Some uu____5780)
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
  fun cb ->
    fun t ->
      fun ea ->
        fun eb ->
          fun er ->
            fun args ->
              let uu____5868 =
                extract_3_nbe cb ea eb
                  FStar_Tactics_Embedding.e_proofstate_nbe args in
              FStar_Util.bind_opt uu____5868
                (fun uu____5889 ->
                   match uu____5889 with
                   | (a, b, ps) ->
                       let r =
                         let uu____5904 = t a b in
                         FStar_Tactics_Basic.run_safe uu____5904 ps in
                       let uu____5907 =
                         let uu____5908 =
                           FStar_Tactics_Embedding.e_result_nbe er in
                         FStar_TypeChecker_NBETerm.embed uu____5908 cb r in
                       FStar_Pervasives_Native.Some uu____5907)
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
  fun cb ->
    fun t ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun er ->
              fun args ->
                let uu____6014 =
                  extract_4_nbe cb ea eb ec
                    FStar_Tactics_Embedding.e_proofstate_nbe args in
                FStar_Util.bind_opt uu____6014
                  (fun uu____6040 ->
                     match uu____6040 with
                     | (a, b, c, ps) ->
                         let r =
                           let uu____6058 = t a b c in
                           FStar_Tactics_Basic.run_safe uu____6058 ps in
                         let uu____6061 =
                           let uu____6062 =
                             FStar_Tactics_Embedding.e_result_nbe er in
                           FStar_TypeChecker_NBETerm.embed uu____6062 cb r in
                         FStar_Pervasives_Native.Some uu____6061)
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
  fun cb ->
    fun t ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun ed ->
              fun er ->
                fun args ->
                  let uu____6187 =
                    extract_5_nbe cb ea eb ec ed
                      FStar_Tactics_Embedding.e_proofstate_nbe args in
                  FStar_Util.bind_opt uu____6187
                    (fun uu____6218 ->
                       match uu____6218 with
                       | (a, b, c, d, ps) ->
                           let r =
                             let uu____6239 = t a b c d in
                             FStar_Tactics_Basic.run_safe uu____6239 ps in
                           let uu____6242 =
                             let uu____6243 =
                               FStar_Tactics_Embedding.e_result_nbe er in
                             FStar_TypeChecker_NBETerm.embed uu____6243 cb r in
                           FStar_Pervasives_Native.Some uu____6242)
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
  fun cb ->
    fun t ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun ed ->
              fun ee ->
                fun er ->
                  fun args ->
                    let uu____6387 =
                      extract_6_nbe cb ea eb ec ed ee
                        FStar_Tactics_Embedding.e_proofstate_nbe args in
                    FStar_Util.bind_opt uu____6387
                      (fun uu____6423 ->
                         match uu____6423 with
                         | (a, b, c, d, e, ps) ->
                             let r =
                               let uu____6447 = t a b c d e in
                               FStar_Tactics_Basic.run_safe uu____6447 ps in
                             let uu____6450 =
                               let uu____6451 =
                                 FStar_Tactics_Embedding.e_result_nbe er in
                               FStar_TypeChecker_NBETerm.embed uu____6451 cb
                                 r in
                             FStar_Pervasives_Native.Some uu____6450)
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
  fun cb ->
    fun t ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun ed ->
              fun ee ->
                fun ef ->
                  fun er ->
                    fun args ->
                      let uu____6614 =
                        extract_7_nbe cb ea eb ec ed ee ef
                          FStar_Tactics_Embedding.e_proofstate_nbe args in
                      FStar_Util.bind_opt uu____6614
                        (fun uu____6655 ->
                           match uu____6655 with
                           | (a, b, c, d, e, f, ps) ->
                               let r =
                                 let uu____6682 = t a b c d e f in
                                 FStar_Tactics_Basic.run_safe uu____6682 ps in
                               let uu____6685 =
                                 let uu____6686 =
                                   FStar_Tactics_Embedding.e_result_nbe er in
                                 FStar_TypeChecker_NBETerm.embed uu____6686
                                   cb r in
                               FStar_Pervasives_Native.Some uu____6685)
let (step_from_native_step :
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Cfg.primitive_step)
  =
  fun s ->
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
        (fun _cb ->
           FStar_TypeChecker_NBETerm.dummy_interp s.FStar_Tactics_Native.name)
    }
let timing_int :
  'Auu____6724 'Auu____6725 'Auu____6726 'Auu____6727 .
    FStar_Ident.lid ->
      ('Auu____6724 -> 'Auu____6725 -> 'Auu____6726 -> 'Auu____6727) ->
        'Auu____6724 -> 'Auu____6725 -> 'Auu____6726 -> 'Auu____6727
  =
  fun l ->
    fun f -> fun psc -> fun cb -> fun args -> let r = f psc cb args in r
let timing_nbe :
  'Auu____6784 'Auu____6785 'Auu____6786 .
    FStar_Ident.lid ->
      ('Auu____6784 -> 'Auu____6785 -> 'Auu____6786) ->
        'Auu____6784 -> 'Auu____6785 -> 'Auu____6786
  = fun l -> fun f -> fun nbe_cbs -> fun args -> let r = f nbe_cbs args in r
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
  fun nm ->
    fun arity ->
      fun nunivs ->
        fun interp ->
          fun nbe_interp ->
            let nm1 =
              FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
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
  fun uu____6906 -> FStar_Tactics_Native.list_all ()
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____6914 ->
    let uu____6915 = native_tactics () in
    FStar_List.map step_from_native_step uu____6915
let rec drop :
  'Auu____6925 .
    Prims.int -> 'Auu____6925 Prims.list -> 'Auu____6925 Prims.list
  =
  fun n1 ->
    fun l ->
      if n1 = (Prims.parse_int "0")
      then l
      else
        (match l with
         | [] -> failwith "drop: impossible"
         | uu____6954::xs -> drop (n1 - (Prims.parse_int "1")) xs)
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
  fun nunivs ->
    fun name ->
      fun f ->
        fun ea ->
          fun er ->
            fun nf ->
              fun nea ->
                fun ner ->
                  mk name (Prims.parse_int "2") nunivs
                    (mk_tactic_interpretation_1 f ea er)
                    (fun cb ->
                       fun args ->
                         let uu____7072 = drop nunivs args in
                         mk_tactic_nbe_interpretation_1 cb nf nea ner
                           uu____7072)
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
  fun nunivs ->
    fun name ->
      fun f ->
        fun ea ->
          fun eb ->
            fun er ->
              fun nf ->
                fun nea ->
                  fun neb ->
                    fun ner ->
                      mk name (Prims.parse_int "3") nunivs
                        (mk_tactic_interpretation_2 f ea eb er)
                        (fun cb ->
                           fun args ->
                             let uu____7228 = drop nunivs args in
                             mk_tactic_nbe_interpretation_2 cb nf nea neb ner
                               uu____7228)
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
  fun nunivs ->
    fun name ->
      fun f ->
        fun ea ->
          fun eb ->
            fun ec ->
              fun er ->
                fun nf ->
                  fun nea ->
                    fun neb ->
                      fun nec ->
                        fun ner ->
                          mk name (Prims.parse_int "4") nunivs
                            (mk_tactic_interpretation_3 f ea eb ec er)
                            (fun cb ->
                               fun args ->
                                 let uu____7422 = drop nunivs args in
                                 mk_tactic_nbe_interpretation_3 cb nf nea neb
                                   nec ner uu____7422)
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
  fun nunivs ->
    fun name ->
      fun f ->
        fun ea ->
          fun eb ->
            fun ec ->
              fun ed ->
                fun er ->
                  fun nf ->
                    fun nea ->
                      fun neb ->
                        fun nec ->
                          fun ned ->
                            fun ner ->
                              mk name (Prims.parse_int "5") nunivs
                                (mk_tactic_interpretation_4 f ea eb ec ed er)
                                (fun cb ->
                                   fun args ->
                                     let uu____7654 = drop nunivs args in
                                     mk_tactic_nbe_interpretation_4 cb nf nea
                                       neb nec ned ner uu____7654)
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
  fun nunivs ->
    fun name ->
      fun f ->
        fun ea ->
          fun eb ->
            fun ec ->
              fun ed ->
                fun ee ->
                  fun er ->
                    fun nf ->
                      fun nea ->
                        fun neb ->
                          fun nec ->
                            fun ned ->
                              fun nee ->
                                fun ner ->
                                  mk name (Prims.parse_int "6") nunivs
                                    (mk_tactic_interpretation_5 f ea eb ec ed
                                       ee er)
                                    (fun cb ->
                                       fun args ->
                                         let uu____7924 = drop nunivs args in
                                         mk_tactic_nbe_interpretation_5 cb nf
                                           nea neb nec ned nee ner uu____7924)
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
  fun nm ->
    fun arity ->
      fun nunivs ->
        fun interp ->
          fun nbe_interp ->
            let nm1 =
              FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
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
  fun f ->
    fun ea ->
      fun er ->
        fun psc ->
          fun ncb ->
            fun args ->
              let uu____8075 = extract_1 ea ncb args in
              FStar_Util.bind_opt uu____8075
                (fun a ->
                   let r = f a in
                   let uu____8083 =
                     let uu____8084 = FStar_TypeChecker_Cfg.psc_range psc in
                     embed er uu____8084 r ncb in
                   FStar_Pervasives_Native.Some uu____8083)
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
  fun f ->
    fun ea ->
      fun eb ->
        fun er ->
          fun psc ->
            fun ncb ->
              fun args ->
                let uu____8170 = extract_2 ea eb ncb args in
                FStar_Util.bind_opt uu____8170
                  (fun uu____8186 ->
                     match uu____8186 with
                     | (a, b) ->
                         let r = f a b in
                         let uu____8196 =
                           let uu____8197 =
                             FStar_TypeChecker_Cfg.psc_range psc in
                           embed er uu____8197 r ncb in
                         FStar_Pervasives_Native.Some uu____8196)
let mk_total_nbe_interpretation_1 :
  'a 'r .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('a -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb ->
    fun f ->
      fun ea ->
        fun er ->
          fun args ->
            let uu____8255 = extract_1_nbe cb ea args in
            FStar_Util.bind_opt uu____8255
              (fun a ->
                 let r = f a in
                 let uu____8263 = FStar_TypeChecker_NBETerm.embed er cb r in
                 FStar_Pervasives_Native.Some uu____8263)
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
  fun cb ->
    fun f ->
      fun ea ->
        fun eb ->
          fun er ->
            fun args ->
              let uu____8340 = extract_2_nbe cb ea eb args in
              FStar_Util.bind_opt uu____8340
                (fun uu____8356 ->
                   match uu____8356 with
                   | (a, b) ->
                       let r = f a b in
                       let uu____8366 =
                         FStar_TypeChecker_NBETerm.embed er cb r in
                       FStar_Pervasives_Native.Some uu____8366)
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
  fun nunivs ->
    fun name ->
      fun f ->
        fun ea ->
          fun er ->
            fun nf ->
              fun nea ->
                fun ner ->
                  mkt name (Prims.parse_int "1") nunivs
                    (mk_total_interpretation_1 f ea er)
                    (fun cb ->
                       fun args ->
                         let uu____8472 = drop nunivs args in
                         mk_total_nbe_interpretation_1 cb nf nea ner
                           uu____8472)
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
  fun nunivs ->
    fun name ->
      fun f ->
        fun ea ->
          fun eb ->
            fun er ->
              fun nf ->
                fun nea ->
                  fun neb ->
                    fun ner ->
                      mkt name (Prims.parse_int "2") nunivs
                        (mk_total_interpretation_2 f ea eb er)
                        (fun cb ->
                           fun args ->
                             let uu____8620 = drop nunivs args in
                             mk_total_nbe_interpretation_2 cb nf nea neb ner
                               uu____8620)