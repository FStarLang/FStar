open Prims
let unembed :
  'Auu____8 .
    'Auu____8 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____8 FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  ->
        let uu____40 = FStar_Syntax_Embeddings.unembed e t  in
        uu____40 true n1
  
let embed :
  'Auu____59 .
    'Auu____59 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____59 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun rng  ->
      fun t  ->
        fun n1  ->
          let uu____90 = FStar_Syntax_Embeddings.embed e t  in
          uu____90 rng FStar_Pervasives_Native.None n1
  
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
        | (a,uu____137)::[] ->
            let uu____178 = unembed ea a ncb  in
            FStar_Util.bind_opt uu____178
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____183 -> failwith "extract_1: wrong number of arguments"
  
let extract_2 :
  'a 'b .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Embeddings.norm_cb ->
          FStar_Syntax_Syntax.args ->
            ('a * 'b) FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ncb  ->
        fun args  ->
          match args with
          | (a,uu____239)::(b,uu____241)::[] ->
              let uu____310 = unembed ea a ncb  in
              FStar_Util.bind_opt uu____310
                (fun a1  ->
                   let uu____320 = unembed eb b ncb  in
                   FStar_Util.bind_opt uu____320
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____333 -> failwith "extract_2: wrong number of arguments"
  
let extract_3 :
  'a 'b 'c .
    'a FStar_Syntax_Embeddings.embedding ->
      'b FStar_Syntax_Embeddings.embedding ->
        'c FStar_Syntax_Embeddings.embedding ->
          FStar_Syntax_Embeddings.norm_cb ->
            FStar_Syntax_Syntax.args ->
              ('a * 'b * 'c) FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ncb  ->
          fun args  ->
            match args with
            | (a,uu____409)::(b,uu____411)::(c,uu____413)::[] ->
                let uu____510 = unembed ea a ncb  in
                FStar_Util.bind_opt uu____510
                  (fun a1  ->
                     let uu____522 = unembed eb b ncb  in
                     FStar_Util.bind_opt uu____522
                       (fun b1  ->
                          let uu____534 = unembed ec c ncb  in
                          FStar_Util.bind_opt uu____534
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____551 -> failwith "extract_3: wrong number of arguments"
  
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
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ncb  ->
            fun args  ->
              match args with
              | (a,uu____645)::(b,uu____647)::(c,uu____649)::(d,uu____651)::[]
                  ->
                  let uu____776 = unembed ea a ncb  in
                  FStar_Util.bind_opt uu____776
                    (fun a1  ->
                       let uu____790 = unembed eb b ncb  in
                       FStar_Util.bind_opt uu____790
                         (fun b1  ->
                            let uu____804 = unembed ec c ncb  in
                            FStar_Util.bind_opt uu____804
                              (fun c1  ->
                                 let uu____818 = unembed ed d ncb  in
                                 FStar_Util.bind_opt uu____818
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____839 -> failwith "extract_4: wrong number of arguments"
  
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
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ee  ->
            fun ncb  ->
              fun args  ->
                match args with
                | (a,uu____951)::(b,uu____953)::(c,uu____955)::(d,uu____957)::
                    (e,uu____959)::[] ->
                    let uu____1112 = unembed ea a ncb  in
                    FStar_Util.bind_opt uu____1112
                      (fun a1  ->
                         let uu____1128 = unembed eb b ncb  in
                         FStar_Util.bind_opt uu____1128
                           (fun b1  ->
                              let uu____1144 = unembed ec c ncb  in
                              FStar_Util.bind_opt uu____1144
                                (fun c1  ->
                                   let uu____1160 = unembed ed d ncb  in
                                   FStar_Util.bind_opt uu____1160
                                     (fun d1  ->
                                        let uu____1176 = unembed ee e ncb  in
                                        FStar_Util.bind_opt uu____1176
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____1201 ->
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
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun ee  ->
            fun ef  ->
              fun ncb  ->
                fun args  ->
                  match args with
                  | (a,uu____1331)::(b,uu____1333)::(c,uu____1335)::(d,uu____1337)::
                      (e,uu____1339)::(f,uu____1341)::[] ->
                      let uu____1522 = unembed ea a ncb  in
                      FStar_Util.bind_opt uu____1522
                        (fun a1  ->
                           let uu____1540 = unembed eb b ncb  in
                           FStar_Util.bind_opt uu____1540
                             (fun b1  ->
                                let uu____1558 = unembed ec c ncb  in
                                FStar_Util.bind_opt uu____1558
                                  (fun c1  ->
                                     let uu____1576 = unembed ed d ncb  in
                                     FStar_Util.bind_opt uu____1576
                                       (fun d1  ->
                                          let uu____1594 = unembed ee e ncb
                                             in
                                          FStar_Util.bind_opt uu____1594
                                            (fun e1  ->
                                               let uu____1612 =
                                                 unembed ef f ncb  in
                                               FStar_Util.bind_opt uu____1612
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____1641 ->
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
                    | (a,uu____1789)::(b,uu____1791)::(c,uu____1793)::
                        (d,uu____1795)::(e,uu____1797)::(f,uu____1799)::
                        (g,uu____1801)::[] ->
                        let uu____2010 = unembed ea a ncb  in
                        FStar_Util.bind_opt uu____2010
                          (fun a1  ->
                             let uu____2030 = unembed eb b ncb  in
                             FStar_Util.bind_opt uu____2030
                               (fun b1  ->
                                  let uu____2050 = unembed ec c ncb  in
                                  FStar_Util.bind_opt uu____2050
                                    (fun c1  ->
                                       let uu____2070 = unembed ed d ncb  in
                                       FStar_Util.bind_opt uu____2070
                                         (fun d1  ->
                                            let uu____2090 = unembed ee e ncb
                                               in
                                            FStar_Util.bind_opt uu____2090
                                              (fun e1  ->
                                                 let uu____2110 =
                                                   unembed ef f ncb  in
                                                 FStar_Util.bind_opt
                                                   uu____2110
                                                   (fun f1  ->
                                                      let uu____2130 =
                                                        unembed eg g ncb  in
                                                      FStar_Util.bind_opt
                                                        uu____2130
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____2163 ->
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
                                  | (a1,uu____2425)::(a2,uu____2427)::
                                      (a3,uu____2429)::(a4,uu____2431)::
                                      (a5,uu____2433)::(a6,uu____2435)::
                                      (a7,uu____2437)::(a8,uu____2439)::
                                      (a9,uu____2441)::(a10,uu____2443)::
                                      (a11,uu____2445)::(a12,uu____2447)::
                                      (a13,uu____2449)::(a14,uu____2451)::[]
                                      ->
                                      let uu____2856 = unembed e_t1 a1 ncb
                                         in
                                      FStar_Util.bind_opt uu____2856
                                        (fun a15  ->
                                           let uu____2890 =
                                             unembed e_t2 a2 ncb  in
                                           FStar_Util.bind_opt uu____2890
                                             (fun a21  ->
                                                let uu____2924 =
                                                  unembed e_t3 a3 ncb  in
                                                FStar_Util.bind_opt
                                                  uu____2924
                                                  (fun a31  ->
                                                     let uu____2958 =
                                                       unembed e_t4 a4 ncb
                                                        in
                                                     FStar_Util.bind_opt
                                                       uu____2958
                                                       (fun a41  ->
                                                          let uu____2992 =
                                                            unembed e_t5 a5
                                                              ncb
                                                             in
                                                          FStar_Util.bind_opt
                                                            uu____2992
                                                            (fun a51  ->
                                                               let uu____3026
                                                                 =
                                                                 unembed e_t6
                                                                   a6 ncb
                                                                  in
                                                               FStar_Util.bind_opt
                                                                 uu____3026
                                                                 (fun a61  ->
                                                                    let uu____3060
                                                                    =
                                                                    unembed
                                                                    e_t7 a7
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____3060
                                                                    (fun a71 
                                                                    ->
                                                                    let uu____3094
                                                                    =
                                                                    unembed
                                                                    e_t8 a8
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____3094
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____3128
                                                                    =
                                                                    unembed
                                                                    e_t9 a9
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____3128
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____3162
                                                                    =
                                                                    unembed
                                                                    e_t10 a10
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____3162
                                                                    (fun a101
                                                                     ->
                                                                    let uu____3196
                                                                    =
                                                                    unembed
                                                                    e_t11 a11
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____3196
                                                                    (fun a111
                                                                     ->
                                                                    let uu____3230
                                                                    =
                                                                    unembed
                                                                    e_t12 a12
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____3230
                                                                    (fun a121
                                                                     ->
                                                                    let uu____3264
                                                                    =
                                                                    unembed
                                                                    e_t13 a13
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____3264
                                                                    (fun a131
                                                                     ->
                                                                    let uu____3298
                                                                    =
                                                                    unembed
                                                                    e_t14 a14
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____3298
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
                                  | uu____3359 ->
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
        | (a,uu____3438)::[] ->
            let uu____3447 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
            FStar_Util.bind_opt uu____3447
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____3452 -> failwith "extract_1_nbe: wrong number of arguments"
  
let extract_2_nbe :
  'a 'b .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          FStar_TypeChecker_NBETerm.args ->
            ('a * 'b) FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun args  ->
          match args with
          | (a,uu____3528)::(b,uu____3530)::[] ->
              let uu____3543 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
              FStar_Util.bind_opt uu____3543
                (fun a1  ->
                   let uu____3553 = FStar_TypeChecker_NBETerm.unembed eb cb b
                      in
                   FStar_Util.bind_opt uu____3553
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____3566 -> failwith "extract_2_nbe: wrong number of arguments"
  
let extract_3_nbe :
  'a 'b 'c .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'a FStar_TypeChecker_NBETerm.embedding ->
        'b FStar_TypeChecker_NBETerm.embedding ->
          'c FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              ('a * 'b * 'c) FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun args  ->
            match args with
            | (a,uu____3669)::(b,uu____3671)::(c,uu____3673)::[] ->
                let uu____3690 = FStar_TypeChecker_NBETerm.unembed ea cb a
                   in
                FStar_Util.bind_opt uu____3690
                  (fun a1  ->
                     let uu____3702 =
                       FStar_TypeChecker_NBETerm.unembed eb cb b  in
                     FStar_Util.bind_opt uu____3702
                       (fun b1  ->
                          let uu____3714 =
                            FStar_TypeChecker_NBETerm.unembed ec cb c  in
                          FStar_Util.bind_opt uu____3714
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____3731 ->
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
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun args  ->
              match args with
              | (a,uu____3859)::(b,uu____3861)::(c,uu____3863)::(d,uu____3865)::[]
                  ->
                  let uu____3886 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____3886
                    (fun a1  ->
                       let uu____3900 =
                         FStar_TypeChecker_NBETerm.unembed eb cb b  in
                       FStar_Util.bind_opt uu____3900
                         (fun b1  ->
                            let uu____3914 =
                              FStar_TypeChecker_NBETerm.unembed ec cb c  in
                            FStar_Util.bind_opt uu____3914
                              (fun c1  ->
                                 let uu____3928 =
                                   FStar_TypeChecker_NBETerm.unembed ed cb d
                                    in
                                 FStar_Util.bind_opt uu____3928
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____3949 ->
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
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun ee  ->
              fun args  ->
                match args with
                | (a,uu____4102)::(b,uu____4104)::(c,uu____4106)::(d,uu____4108)::
                    (e,uu____4110)::[] ->
                    let uu____4135 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____4135
                      (fun a1  ->
                         let uu____4151 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____4151
                           (fun b1  ->
                              let uu____4167 =
                                FStar_TypeChecker_NBETerm.unembed ec cb c  in
                              FStar_Util.bind_opt uu____4167
                                (fun c1  ->
                                   let uu____4183 =
                                     FStar_TypeChecker_NBETerm.unembed ed cb
                                       d
                                      in
                                   FStar_Util.bind_opt uu____4183
                                     (fun d1  ->
                                        let uu____4199 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            ee cb e
                                           in
                                        FStar_Util.bind_opt uu____4199
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____4224 ->
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
  fun cb  ->
    fun ea  ->
      fun eb  ->
        fun ec  ->
          fun ed  ->
            fun ee  ->
              fun ef  ->
                fun args  ->
                  match args with
                  | (a,uu____4402)::(b,uu____4404)::(c,uu____4406)::(d,uu____4408)::
                      (e,uu____4410)::(f,uu____4412)::[] ->
                      let uu____4441 =
                        FStar_TypeChecker_NBETerm.unembed ea cb a  in
                      FStar_Util.bind_opt uu____4441
                        (fun a1  ->
                           let uu____4459 =
                             FStar_TypeChecker_NBETerm.unembed eb cb b  in
                           FStar_Util.bind_opt uu____4459
                             (fun b1  ->
                                let uu____4477 =
                                  FStar_TypeChecker_NBETerm.unembed ec cb c
                                   in
                                FStar_Util.bind_opt uu____4477
                                  (fun c1  ->
                                     let uu____4495 =
                                       FStar_TypeChecker_NBETerm.unembed ed
                                         cb d
                                        in
                                     FStar_Util.bind_opt uu____4495
                                       (fun d1  ->
                                          let uu____4513 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              ee cb e
                                             in
                                          FStar_Util.bind_opt uu____4513
                                            (fun e1  ->
                                               let uu____4531 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   ef cb f
                                                  in
                                               FStar_Util.bind_opt uu____4531
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____4560 ->
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
                    | (a,uu____4763)::(b,uu____4765)::(c,uu____4767)::
                        (d,uu____4769)::(e,uu____4771)::(f,uu____4773)::
                        (g,uu____4775)::[] ->
                        let uu____4808 =
                          FStar_TypeChecker_NBETerm.unembed ea cb a  in
                        FStar_Util.bind_opt uu____4808
                          (fun a1  ->
                             let uu____4828 =
                               FStar_TypeChecker_NBETerm.unembed eb cb b  in
                             FStar_Util.bind_opt uu____4828
                               (fun b1  ->
                                  let uu____4848 =
                                    FStar_TypeChecker_NBETerm.unembed ec cb c
                                     in
                                  FStar_Util.bind_opt uu____4848
                                    (fun c1  ->
                                       let uu____4868 =
                                         FStar_TypeChecker_NBETerm.unembed ed
                                           cb d
                                          in
                                       FStar_Util.bind_opt uu____4868
                                         (fun d1  ->
                                            let uu____4888 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                ee cb e
                                               in
                                            FStar_Util.bind_opt uu____4888
                                              (fun e1  ->
                                                 let uu____4908 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     ef cb f
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____4908
                                                   (fun f1  ->
                                                      let uu____4928 =
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          eg cb g
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____4928
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____4961 ->
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
              let uu____5057 =
                extract_2 ea FStar_Tactics_Embedding.e_proofstate ncb args
                 in
              FStar_Util.bind_opt uu____5057
                (fun uu____5279  ->
                   match uu____5279 with
                   | (a,ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let r =
                         let uu____5631 = t a  in
                         FStar_Tactics_Basic.run_safe uu____5631 ps1  in
                       let uu____5634 =
                         let uu____5643 = FStar_Tactics_Embedding.e_result er
                            in
                         let uu____5648 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         embed uu____5643 uu____5648 r ncb  in
                       FStar_Pervasives_Native.Some uu____5634)
  
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
                let uu____5752 =
                  extract_3 ea eb FStar_Tactics_Embedding.e_proofstate ncb
                    args
                   in
                FStar_Util.bind_opt uu____5752
                  (fun uu____5979  ->
                     match uu____5979 with
                     | (a,b,ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let r =
                           let uu____6334 = t a b  in
                           FStar_Tactics_Basic.run_safe uu____6334 ps1  in
                         let uu____6337 =
                           let uu____6346 =
                             FStar_Tactics_Embedding.e_result er  in
                           let uu____6351 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed uu____6346 uu____6351 r ncb  in
                         FStar_Pervasives_Native.Some uu____6337)
  
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
                  let uu____6474 =
                    extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                      ncb args
                     in
                  FStar_Util.bind_opt uu____6474
                    (fun uu____6706  ->
                       match uu____6706 with
                       | (a,b,c,ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let r =
                             let uu____7064 = t a b c  in
                             FStar_Tactics_Basic.run_safe uu____7064 ps1  in
                           let uu____7067 =
                             let uu____7076 =
                               FStar_Tactics_Embedding.e_result er  in
                             let uu____7081 =
                               FStar_TypeChecker_Cfg.psc_range psc  in
                             embed uu____7076 uu____7081 r ncb  in
                           FStar_Pervasives_Native.Some uu____7067)
  
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
                    let uu____7223 =
                      extract_5 ea eb ec ed
                        FStar_Tactics_Embedding.e_proofstate ncb args
                       in
                    FStar_Util.bind_opt uu____7223
                      (fun uu____7460  ->
                         match uu____7460 with
                         | (a,b,c,d,ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let r =
                               let uu____7821 = t a b c d  in
                               FStar_Tactics_Basic.run_safe uu____7821 ps1
                                in
                             let uu____7824 =
                               let uu____7833 =
                                 FStar_Tactics_Embedding.e_result er  in
                               let uu____7838 =
                                 FStar_TypeChecker_Cfg.psc_range psc  in
                               embed uu____7833 uu____7838 r ncb  in
                             FStar_Pervasives_Native.Some uu____7824)
  
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
                      let uu____7999 =
                        extract_6 ea eb ec ed ee
                          FStar_Tactics_Embedding.e_proofstate ncb args
                         in
                      FStar_Util.bind_opt uu____7999
                        (fun uu____8241  ->
                           match uu____8241 with
                           | (a,b,c,d,e,ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let r =
                                 let uu____8605 = t a b c d e  in
                                 FStar_Tactics_Basic.run_safe uu____8605 ps1
                                  in
                               let uu____8608 =
                                 let uu____8617 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____8622 =
                                   FStar_TypeChecker_Cfg.psc_range psc  in
                                 embed uu____8617 uu____8622 r ncb  in
                               FStar_Pervasives_Native.Some uu____8608)
  
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
                        let uu____8802 =
                          extract_7 ea eb ec ed ee ef
                            FStar_Tactics_Embedding.e_proofstate ncb args
                           in
                        FStar_Util.bind_opt uu____8802
                          (fun uu____9049  ->
                             match uu____9049 with
                             | (a,b,c,d,e,f,ps) ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 let r =
                                   let uu____9416 = t a b c d e f  in
                                   FStar_Tactics_Basic.run_safe uu____9416
                                     ps1
                                    in
                                 let uu____9419 =
                                   let uu____9428 =
                                     FStar_Tactics_Embedding.e_result er  in
                                   let uu____9433 =
                                     FStar_TypeChecker_Cfg.psc_range psc  in
                                   embed uu____9428 uu____9433 r ncb  in
                                 FStar_Pervasives_Native.Some uu____9419)
  
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
                                      let uu____9746 =
                                        extract_14 e_t1 e_t2 e_t3 e_t4 e_t5
                                          e_t6 e_t7 e_t8 e_t9 e_t10 e_t11
                                          e_t12 e_t13
                                          FStar_Tactics_Embedding.e_proofstate
                                          ncb args
                                         in
                                      FStar_Util.bind_opt uu____9746
                                        (fun uu____10028  ->
                                           match uu____10028 with
                                           | (a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,ps)
                                               ->
                                               let ps1 =
                                                 FStar_Tactics_Types.set_ps_psc
                                                   psc ps
                                                  in
                                               let r =
                                                 let uu____10416 =
                                                   t a1 a2 a3 a4 a5 a6 a7 a8
                                                     a9 a10 a11 a12 a13
                                                    in
                                                 FStar_Tactics_Basic.run_safe
                                                   uu____10416 ps1
                                                  in
                                               let uu____10419 =
                                                 let uu____10428 =
                                                   FStar_Tactics_Embedding.e_result
                                                     er
                                                    in
                                                 let uu____10433 =
                                                   FStar_TypeChecker_Cfg.psc_range
                                                     psc
                                                    in
                                                 embed uu____10428
                                                   uu____10433 r ncb
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10419)
  
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
            let uu____10523 =
              extract_2_nbe cb ea FStar_Tactics_Embedding.e_proofstate_nbe
                args
               in
            FStar_Util.bind_opt uu____10523
              (fun uu____10740  ->
                 match uu____10740 with
                 | (a,ps) ->
                     let r =
                       let uu____10953 = t a  in
                       FStar_Tactics_Basic.run_safe uu____10953 ps  in
                     let uu____10956 =
                       let uu____10957 =
                         FStar_Tactics_Embedding.e_result_nbe er  in
                       FStar_TypeChecker_NBETerm.embed uu____10957 cb r  in
                     FStar_Pervasives_Native.Some uu____10956)
  
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
              let uu____11080 =
                extract_3_nbe cb ea eb
                  FStar_Tactics_Embedding.e_proofstate_nbe args
                 in
              FStar_Util.bind_opt uu____11080
                (fun uu____11302  ->
                   match uu____11302 with
                   | (a,b,ps) ->
                       let r =
                         let uu____11518 = t a b  in
                         FStar_Tactics_Basic.run_safe uu____11518 ps  in
                       let uu____11521 =
                         let uu____11522 =
                           FStar_Tactics_Embedding.e_result_nbe er  in
                         FStar_TypeChecker_NBETerm.embed uu____11522 cb r  in
                       FStar_Pervasives_Native.Some uu____11521)
  
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
                let uu____11671 =
                  extract_4_nbe cb ea eb ec
                    FStar_Tactics_Embedding.e_proofstate_nbe args
                   in
                FStar_Util.bind_opt uu____11671
                  (fun uu____11898  ->
                     match uu____11898 with
                     | (a,b,c,ps) ->
                         let r =
                           let uu____12117 = t a b c  in
                           FStar_Tactics_Basic.run_safe uu____12117 ps  in
                         let uu____12120 =
                           let uu____12121 =
                             FStar_Tactics_Embedding.e_result_nbe er  in
                           FStar_TypeChecker_NBETerm.embed uu____12121 cb r
                            in
                         FStar_Pervasives_Native.Some uu____12120)
  
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
                  let uu____12296 =
                    extract_5_nbe cb ea eb ec ed
                      FStar_Tactics_Embedding.e_proofstate_nbe args
                     in
                  FStar_Util.bind_opt uu____12296
                    (fun uu____12528  ->
                       match uu____12528 with
                       | (a,b,c,d,ps) ->
                           let r =
                             let uu____12750 = t a b c d  in
                             FStar_Tactics_Basic.run_safe uu____12750 ps  in
                           let uu____12753 =
                             let uu____12754 =
                               FStar_Tactics_Embedding.e_result_nbe er  in
                             FStar_TypeChecker_NBETerm.embed uu____12754 cb r
                              in
                           FStar_Pervasives_Native.Some uu____12753)
  
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
                    let uu____12955 =
                      extract_6_nbe cb ea eb ec ed ee
                        FStar_Tactics_Embedding.e_proofstate_nbe args
                       in
                    FStar_Util.bind_opt uu____12955
                      (fun uu____13192  ->
                         match uu____13192 with
                         | (a,b,c,d,e,ps) ->
                             let r =
                               let uu____13417 = t a b c d e  in
                               FStar_Tactics_Basic.run_safe uu____13417 ps
                                in
                             let uu____13420 =
                               let uu____13421 =
                                 FStar_Tactics_Embedding.e_result_nbe er  in
                               FStar_TypeChecker_NBETerm.embed uu____13421 cb
                                 r
                                in
                             FStar_Pervasives_Native.Some uu____13420)
  
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
                      let uu____13648 =
                        extract_7_nbe cb ea eb ec ed ee ef
                          FStar_Tactics_Embedding.e_proofstate_nbe args
                         in
                      FStar_Util.bind_opt uu____13648
                        (fun uu____13890  ->
                           match uu____13890 with
                           | (a,b,c,d,e,f,ps) ->
                               let r =
                                 let uu____14118 = t a b c d e f  in
                                 FStar_Tactics_Basic.run_safe uu____14118 ps
                                  in
                               let uu____14121 =
                                 let uu____14122 =
                                   FStar_Tactics_Embedding.e_result_nbe er
                                    in
                                 FStar_TypeChecker_NBETerm.embed uu____14122
                                   cb r
                                  in
                               FStar_Pervasives_Native.Some uu____14121)
  
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
  'Auu____14211 'Auu____14212 'Auu____14213 'Auu____14214 .
    FStar_Ident.lid ->
      ('Auu____14211 -> 'Auu____14212 -> 'Auu____14213 -> 'Auu____14214) ->
        'Auu____14211 -> 'Auu____14212 -> 'Auu____14213 -> 'Auu____14214
  =
  fun l  ->
    fun f  -> fun psc  -> fun cb  -> fun args  -> let r = f psc cb args  in r
  
let timing_nbe :
  'Auu____14279 'Auu____14280 'Auu____14281 .
    FStar_Ident.lid ->
      ('Auu____14279 -> 'Auu____14280 -> 'Auu____14281) ->
        'Auu____14279 -> 'Auu____14280 -> 'Auu____14281
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
  fun uu____14467  -> FStar_Tactics_Native.list_all () 
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____14487  ->
    let uu____14488 = native_tactics ()  in
    FStar_List.map step_from_native_step uu____14488
  
let rec drop :
  'Auu____14526 .
    Prims.int -> 'Auu____14526 Prims.list -> 'Auu____14526 Prims.list
  =
  fun n1  ->
    fun l  ->
      if n1 = (Prims.parse_int "0")
      then l
      else
        (match l with
         | [] -> failwith "drop: impossible"
         | uu____14555::xs -> drop (n1 - (Prims.parse_int "1")) xs)
  
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
                         let uu____14703 = drop nunivs args  in
                         mk_tactic_nbe_interpretation_1 cb nf nea ner
                           uu____14703)
  
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
                             let uu____14896 = drop nunivs args  in
                             mk_tactic_nbe_interpretation_2 cb nf nea neb ner
                               uu____14896)
  
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
                                 let uu____15134 = drop nunivs args  in
                                 mk_tactic_nbe_interpretation_3 cb nf nea neb
                                   nec ner uu____15134)
  
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
                                     let uu____15417 = drop nunivs args  in
                                     mk_tactic_nbe_interpretation_4 cb nf nea
                                       neb nec ned ner uu____15417)
  
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
                                         let uu____15745 = drop nunivs args
                                            in
                                         mk_tactic_nbe_interpretation_5 cb nf
                                           nea neb nec ned nee ner
                                           uu____15745)
  
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
              let uu____15954 = extract_1 ea ncb args  in
              FStar_Util.bind_opt uu____15954
                (fun a  ->
                   let r = f a  in
                   let uu____15966 =
                     let uu____15975 = FStar_TypeChecker_Cfg.psc_range psc
                        in
                     embed er uu____15975 r ncb  in
                   FStar_Pervasives_Native.Some uu____15966)
  
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
                let uu____16073 = extract_2 ea eb ncb args  in
                FStar_Util.bind_opt uu____16073
                  (fun uu____16093  ->
                     match uu____16093 with
                     | (a,b) ->
                         let r = f a b  in
                         let uu____16107 =
                           let uu____16116 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed er uu____16116 r ncb  in
                         FStar_Pervasives_Native.Some uu____16107)
  
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
            let uu____16200 = extract_1_nbe cb ea args  in
            FStar_Util.bind_opt uu____16200
              (fun a  ->
                 let r = f a  in
                 let uu____16208 = FStar_TypeChecker_NBETerm.embed er cb r
                    in
                 FStar_Pervasives_Native.Some uu____16208)
  
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
              let uu____16314 = extract_2_nbe cb ea eb args  in
              FStar_Util.bind_opt uu____16314
                (fun uu____16330  ->
                   match uu____16330 with
                   | (a,b) ->
                       let r = f a b  in
                       let uu____16340 =
                         FStar_TypeChecker_NBETerm.embed er cb r  in
                       FStar_Pervasives_Native.Some uu____16340)
  
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
                         let uu____16476 = drop nunivs args  in
                         mk_total_nbe_interpretation_1 cb nf nea ner
                           uu____16476)
  
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
                             let uu____16661 = drop nunivs args  in
                             mk_total_nbe_interpretation_2 cb nf nea neb ner
                               uu____16661)
  