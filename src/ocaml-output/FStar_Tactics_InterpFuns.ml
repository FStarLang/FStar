open Prims
let unembed :
  'Auu____67225 .
    'Auu____67225 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____67225 FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  ->
        let uu____67251 = FStar_Syntax_Embeddings.unembed e t  in
        uu____67251 true n1
  
let embed :
  'Auu____67276 .
    'Auu____67276 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____67276 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun rng  ->
      fun t  ->
        fun n1  ->
          let uu____67305 = FStar_Syntax_Embeddings.embed e t  in
          uu____67305 rng FStar_Pervasives_Native.None n1
  
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
        | (a,uu____67375)::[] ->
            let uu____67400 = unembed ea a ncb  in
            FStar_Util.bind_opt uu____67400
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____67407 -> failwith "extract_1: wrong number of arguments"
  
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
          | (a,uu____67465)::(b,uu____67467)::[] ->
              let uu____67508 = unembed ea a ncb  in
              FStar_Util.bind_opt uu____67508
                (fun a1  ->
                   let uu____67520 = unembed eb b ncb  in
                   FStar_Util.bind_opt uu____67520
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____67535 -> failwith "extract_2: wrong number of arguments"
  
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
            | (a,uu____67613)::(b,uu____67615)::(c,uu____67617)::[] ->
                let uu____67674 = unembed ea a ncb  in
                FStar_Util.bind_opt uu____67674
                  (fun a1  ->
                     let uu____67688 = unembed eb b ncb  in
                     FStar_Util.bind_opt uu____67688
                       (fun b1  ->
                          let uu____67702 = unembed ec c ncb  in
                          FStar_Util.bind_opt uu____67702
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____67721 -> failwith "extract_3: wrong number of arguments"
  
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
              | (a,uu____67817)::(b,uu____67819)::(c,uu____67821)::(d,uu____67823)::[]
                  ->
                  let uu____67896 = unembed ea a ncb  in
                  FStar_Util.bind_opt uu____67896
                    (fun a1  ->
                       let uu____67912 = unembed eb b ncb  in
                       FStar_Util.bind_opt uu____67912
                         (fun b1  ->
                            let uu____67928 = unembed ec c ncb  in
                            FStar_Util.bind_opt uu____67928
                              (fun c1  ->
                                 let uu____67944 = unembed ed d ncb  in
                                 FStar_Util.bind_opt uu____67944
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____67967 ->
                  failwith "extract_4: wrong number of arguments"
  
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
                | (a,uu____68081)::(b,uu____68083)::(c,uu____68085)::
                    (d,uu____68087)::(e,uu____68089)::[] ->
                    let uu____68178 = unembed ea a ncb  in
                    FStar_Util.bind_opt uu____68178
                      (fun a1  ->
                         let uu____68196 = unembed eb b ncb  in
                         FStar_Util.bind_opt uu____68196
                           (fun b1  ->
                              let uu____68214 = unembed ec c ncb  in
                              FStar_Util.bind_opt uu____68214
                                (fun c1  ->
                                   let uu____68232 = unembed ed d ncb  in
                                   FStar_Util.bind_opt uu____68232
                                     (fun d1  ->
                                        let uu____68250 = unembed ee e ncb
                                           in
                                        FStar_Util.bind_opt uu____68250
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____68277 ->
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
                  | (a,uu____68409)::(b,uu____68411)::(c,uu____68413)::
                      (d,uu____68415)::(e,uu____68417)::(f,uu____68419)::[]
                      ->
                      let uu____68524 = unembed ea a ncb  in
                      FStar_Util.bind_opt uu____68524
                        (fun a1  ->
                           let uu____68544 = unembed eb b ncb  in
                           FStar_Util.bind_opt uu____68544
                             (fun b1  ->
                                let uu____68564 = unembed ec c ncb  in
                                FStar_Util.bind_opt uu____68564
                                  (fun c1  ->
                                     let uu____68584 = unembed ed d ncb  in
                                     FStar_Util.bind_opt uu____68584
                                       (fun d1  ->
                                          let uu____68604 = unembed ee e ncb
                                             in
                                          FStar_Util.bind_opt uu____68604
                                            (fun e1  ->
                                               let uu____68624 =
                                                 unembed ef f ncb  in
                                               FStar_Util.bind_opt
                                                 uu____68624
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____68655 ->
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
                    | (a,uu____68805)::(b,uu____68807)::(c,uu____68809)::
                        (d,uu____68811)::(e,uu____68813)::(f,uu____68815)::
                        (g,uu____68817)::[] ->
                        let uu____68938 = unembed ea a ncb  in
                        FStar_Util.bind_opt uu____68938
                          (fun a1  ->
                             let uu____68960 = unembed eb b ncb  in
                             FStar_Util.bind_opt uu____68960
                               (fun b1  ->
                                  let uu____68982 = unembed ec c ncb  in
                                  FStar_Util.bind_opt uu____68982
                                    (fun c1  ->
                                       let uu____69004 = unembed ed d ncb  in
                                       FStar_Util.bind_opt uu____69004
                                         (fun d1  ->
                                            let uu____69026 =
                                              unembed ee e ncb  in
                                            FStar_Util.bind_opt uu____69026
                                              (fun e1  ->
                                                 let uu____69048 =
                                                   unembed ef f ncb  in
                                                 FStar_Util.bind_opt
                                                   uu____69048
                                                   (fun f1  ->
                                                      let uu____69070 =
                                                        unembed eg g ncb  in
                                                      FStar_Util.bind_opt
                                                        uu____69070
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____69105 ->
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
                                  | (a1,uu____69369)::(a2,uu____69371)::
                                      (a3,uu____69373)::(a4,uu____69375)::
                                      (a5,uu____69377)::(a6,uu____69379)::
                                      (a7,uu____69381)::(a8,uu____69383)::
                                      (a9,uu____69385)::(a10,uu____69387)::
                                      (a11,uu____69389)::(a12,uu____69391)::
                                      (a13,uu____69393)::(a14,uu____69395)::[]
                                      ->
                                      let uu____69628 = unembed e_t1 a1 ncb
                                         in
                                      FStar_Util.bind_opt uu____69628
                                        (fun a15  ->
                                           let uu____69664 =
                                             unembed e_t2 a2 ncb  in
                                           FStar_Util.bind_opt uu____69664
                                             (fun a21  ->
                                                let uu____69700 =
                                                  unembed e_t3 a3 ncb  in
                                                FStar_Util.bind_opt
                                                  uu____69700
                                                  (fun a31  ->
                                                     let uu____69736 =
                                                       unembed e_t4 a4 ncb
                                                        in
                                                     FStar_Util.bind_opt
                                                       uu____69736
                                                       (fun a41  ->
                                                          let uu____69772 =
                                                            unembed e_t5 a5
                                                              ncb
                                                             in
                                                          FStar_Util.bind_opt
                                                            uu____69772
                                                            (fun a51  ->
                                                               let uu____69808
                                                                 =
                                                                 unembed e_t6
                                                                   a6 ncb
                                                                  in
                                                               FStar_Util.bind_opt
                                                                 uu____69808
                                                                 (fun a61  ->
                                                                    let uu____69844
                                                                    =
                                                                    unembed
                                                                    e_t7 a7
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____69844
                                                                    (fun a71 
                                                                    ->
                                                                    let uu____69880
                                                                    =
                                                                    unembed
                                                                    e_t8 a8
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____69880
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____69916
                                                                    =
                                                                    unembed
                                                                    e_t9 a9
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____69916
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____69952
                                                                    =
                                                                    unembed
                                                                    e_t10 a10
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____69952
                                                                    (fun a101
                                                                     ->
                                                                    let uu____69988
                                                                    =
                                                                    unembed
                                                                    e_t11 a11
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____69988
                                                                    (fun a111
                                                                     ->
                                                                    let uu____70024
                                                                    =
                                                                    unembed
                                                                    e_t12 a12
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____70024
                                                                    (fun a121
                                                                     ->
                                                                    let uu____70060
                                                                    =
                                                                    unembed
                                                                    e_t13 a13
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____70060
                                                                    (fun a131
                                                                     ->
                                                                    let uu____70096
                                                                    =
                                                                    unembed
                                                                    e_t14 a14
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____70096
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
                                  | uu____70159 ->
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
        | (a,uu____70223)::[] ->
            let uu____70232 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
            FStar_Util.bind_opt uu____70232
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____70237 -> failwith "extract_1_nbe: wrong number of arguments"
  
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
          | (a,uu____70291)::(b,uu____70293)::[] ->
              let uu____70306 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
              FStar_Util.bind_opt uu____70306
                (fun a1  ->
                   let uu____70316 =
                     FStar_TypeChecker_NBETerm.unembed eb cb b  in
                   FStar_Util.bind_opt uu____70316
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____70329 ->
              failwith "extract_2_nbe: wrong number of arguments"
  
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
            | (a,uu____70403)::(b,uu____70405)::(c,uu____70407)::[] ->
                let uu____70424 = FStar_TypeChecker_NBETerm.unembed ea cb a
                   in
                FStar_Util.bind_opt uu____70424
                  (fun a1  ->
                     let uu____70436 =
                       FStar_TypeChecker_NBETerm.unembed eb cb b  in
                     FStar_Util.bind_opt uu____70436
                       (fun b1  ->
                          let uu____70448 =
                            FStar_TypeChecker_NBETerm.unembed ec cb c  in
                          FStar_Util.bind_opt uu____70448
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____70465 ->
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
              | (a,uu____70557)::(b,uu____70559)::(c,uu____70561)::(d,uu____70563)::[]
                  ->
                  let uu____70584 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____70584
                    (fun a1  ->
                       let uu____70598 =
                         FStar_TypeChecker_NBETerm.unembed eb cb b  in
                       FStar_Util.bind_opt uu____70598
                         (fun b1  ->
                            let uu____70612 =
                              FStar_TypeChecker_NBETerm.unembed ec cb c  in
                            FStar_Util.bind_opt uu____70612
                              (fun c1  ->
                                 let uu____70626 =
                                   FStar_TypeChecker_NBETerm.unembed ed cb d
                                    in
                                 FStar_Util.bind_opt uu____70626
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____70647 ->
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
                | (a,uu____70757)::(b,uu____70759)::(c,uu____70761)::
                    (d,uu____70763)::(e,uu____70765)::[] ->
                    let uu____70790 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____70790
                      (fun a1  ->
                         let uu____70806 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____70806
                           (fun b1  ->
                              let uu____70822 =
                                FStar_TypeChecker_NBETerm.unembed ec cb c  in
                              FStar_Util.bind_opt uu____70822
                                (fun c1  ->
                                   let uu____70838 =
                                     FStar_TypeChecker_NBETerm.unembed ed cb
                                       d
                                      in
                                   FStar_Util.bind_opt uu____70838
                                     (fun d1  ->
                                        let uu____70854 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            ee cb e
                                           in
                                        FStar_Util.bind_opt uu____70854
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____70879 ->
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
                  | (a,uu____71007)::(b,uu____71009)::(c,uu____71011)::
                      (d,uu____71013)::(e,uu____71015)::(f,uu____71017)::[]
                      ->
                      let uu____71046 =
                        FStar_TypeChecker_NBETerm.unembed ea cb a  in
                      FStar_Util.bind_opt uu____71046
                        (fun a1  ->
                           let uu____71064 =
                             FStar_TypeChecker_NBETerm.unembed eb cb b  in
                           FStar_Util.bind_opt uu____71064
                             (fun b1  ->
                                let uu____71082 =
                                  FStar_TypeChecker_NBETerm.unembed ec cb c
                                   in
                                FStar_Util.bind_opt uu____71082
                                  (fun c1  ->
                                     let uu____71100 =
                                       FStar_TypeChecker_NBETerm.unembed ed
                                         cb d
                                        in
                                     FStar_Util.bind_opt uu____71100
                                       (fun d1  ->
                                          let uu____71118 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              ee cb e
                                             in
                                          FStar_Util.bind_opt uu____71118
                                            (fun e1  ->
                                               let uu____71136 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   ef cb f
                                                  in
                                               FStar_Util.bind_opt
                                                 uu____71136
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____71165 ->
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
                    | (a,uu____71311)::(b,uu____71313)::(c,uu____71315)::
                        (d,uu____71317)::(e,uu____71319)::(f,uu____71321)::
                        (g,uu____71323)::[] ->
                        let uu____71356 =
                          FStar_TypeChecker_NBETerm.unembed ea cb a  in
                        FStar_Util.bind_opt uu____71356
                          (fun a1  ->
                             let uu____71376 =
                               FStar_TypeChecker_NBETerm.unembed eb cb b  in
                             FStar_Util.bind_opt uu____71376
                               (fun b1  ->
                                  let uu____71396 =
                                    FStar_TypeChecker_NBETerm.unembed ec cb c
                                     in
                                  FStar_Util.bind_opt uu____71396
                                    (fun c1  ->
                                       let uu____71416 =
                                         FStar_TypeChecker_NBETerm.unembed ed
                                           cb d
                                          in
                                       FStar_Util.bind_opt uu____71416
                                         (fun d1  ->
                                            let uu____71436 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                ee cb e
                                               in
                                            FStar_Util.bind_opt uu____71436
                                              (fun e1  ->
                                                 let uu____71456 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     ef cb f
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____71456
                                                   (fun f1  ->
                                                      let uu____71476 =
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          eg cb g
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____71476
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____71509 ->
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
              let uu____71599 =
                extract_2 ea FStar_Tactics_Embedding.e_proofstate ncb args
                 in
              FStar_Util.bind_opt uu____71599
                (fun uu____71618  ->
                   match uu____71618 with
                   | (a,ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let r =
                         let uu____71631 = t a  in
                         FStar_Tactics_Basic.run_safe uu____71631 ps1  in
                       let uu____71634 =
                         let uu____71635 =
                           FStar_Tactics_Embedding.e_result er  in
                         let uu____71640 =
                           FStar_TypeChecker_Cfg.psc_range psc  in
                         embed uu____71635 uu____71640 r ncb  in
                       FStar_Pervasives_Native.Some uu____71634)
  
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
                let uu____71736 =
                  extract_3 ea eb FStar_Tactics_Embedding.e_proofstate ncb
                    args
                   in
                FStar_Util.bind_opt uu____71736
                  (fun uu____71760  ->
                     match uu____71760 with
                     | (a,b,ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let r =
                           let uu____71776 = t a b  in
                           FStar_Tactics_Basic.run_safe uu____71776 ps1  in
                         let uu____71779 =
                           let uu____71780 =
                             FStar_Tactics_Embedding.e_result er  in
                           let uu____71785 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed uu____71780 uu____71785 r ncb  in
                         FStar_Pervasives_Native.Some uu____71779)
  
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
                  let uu____71900 =
                    extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                      ncb args
                     in
                  FStar_Util.bind_opt uu____71900
                    (fun uu____71929  ->
                       match uu____71929 with
                       | (a,b,c,ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let r =
                             let uu____71948 = t a b c  in
                             FStar_Tactics_Basic.run_safe uu____71948 ps1  in
                           let uu____71951 =
                             let uu____71952 =
                               FStar_Tactics_Embedding.e_result er  in
                             let uu____71957 =
                               FStar_TypeChecker_Cfg.psc_range psc  in
                             embed uu____71952 uu____71957 r ncb  in
                           FStar_Pervasives_Native.Some uu____71951)
  
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
                    let uu____72091 =
                      extract_5 ea eb ec ed
                        FStar_Tactics_Embedding.e_proofstate ncb args
                       in
                    FStar_Util.bind_opt uu____72091
                      (fun uu____72125  ->
                         match uu____72125 with
                         | (a,b,c,d,ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let r =
                               let uu____72147 = t a b c d  in
                               FStar_Tactics_Basic.run_safe uu____72147 ps1
                                in
                             let uu____72150 =
                               let uu____72151 =
                                 FStar_Tactics_Embedding.e_result er  in
                               let uu____72156 =
                                 FStar_TypeChecker_Cfg.psc_range psc  in
                               embed uu____72151 uu____72156 r ncb  in
                             FStar_Pervasives_Native.Some uu____72150)
  
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
                      let uu____72309 =
                        extract_6 ea eb ec ed ee
                          FStar_Tactics_Embedding.e_proofstate ncb args
                         in
                      FStar_Util.bind_opt uu____72309
                        (fun uu____72348  ->
                           match uu____72348 with
                           | (a,b,c,d,e,ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let r =
                                 let uu____72373 = t a b c d e  in
                                 FStar_Tactics_Basic.run_safe uu____72373 ps1
                                  in
                               let uu____72376 =
                                 let uu____72377 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____72382 =
                                   FStar_TypeChecker_Cfg.psc_range psc  in
                                 embed uu____72377 uu____72382 r ncb  in
                               FStar_Pervasives_Native.Some uu____72376)
  
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
                        let uu____72554 =
                          extract_7 ea eb ec ed ee ef
                            FStar_Tactics_Embedding.e_proofstate ncb args
                           in
                        FStar_Util.bind_opt uu____72554
                          (fun uu____72598  ->
                             match uu____72598 with
                             | (a,b,c,d,e,f,ps) ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 let r =
                                   let uu____72626 = t a b c d e f  in
                                   FStar_Tactics_Basic.run_safe uu____72626
                                     ps1
                                    in
                                 let uu____72629 =
                                   let uu____72630 =
                                     FStar_Tactics_Embedding.e_result er  in
                                   let uu____72635 =
                                     FStar_TypeChecker_Cfg.psc_range psc  in
                                   embed uu____72630 uu____72635 r ncb  in
                                 FStar_Pervasives_Native.Some uu____72629)
  
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
                                      let uu____72940 =
                                        extract_14 e_t1 e_t2 e_t3 e_t4 e_t5
                                          e_t6 e_t7 e_t8 e_t9 e_t10 e_t11
                                          e_t12 e_t13
                                          FStar_Tactics_Embedding.e_proofstate
                                          ncb args
                                         in
                                      FStar_Util.bind_opt uu____72940
                                        (fun uu____73019  ->
                                           match uu____73019 with
                                           | (a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,ps)
                                               ->
                                               let ps1 =
                                                 FStar_Tactics_Types.set_ps_psc
                                                   psc ps
                                                  in
                                               let r =
                                                 let uu____73068 =
                                                   t a1 a2 a3 a4 a5 a6 a7 a8
                                                     a9 a10 a11 a12 a13
                                                    in
                                                 FStar_Tactics_Basic.run_safe
                                                   uu____73068 ps1
                                                  in
                                               let uu____73071 =
                                                 let uu____73072 =
                                                   FStar_Tactics_Embedding.e_result
                                                     er
                                                    in
                                                 let uu____73077 =
                                                   FStar_TypeChecker_Cfg.psc_range
                                                     psc
                                                    in
                                                 embed uu____73072
                                                   uu____73077 r ncb
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____73071)
  
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
            let uu____73143 =
              extract_2_nbe cb ea FStar_Tactics_Embedding.e_proofstate_nbe
                args
               in
            FStar_Util.bind_opt uu____73143
              (fun uu____73159  ->
                 match uu____73159 with
                 | (a,ps) ->
                     let r =
                       let uu____73171 = t a  in
                       FStar_Tactics_Basic.run_safe uu____73171 ps  in
                     let uu____73174 =
                       let uu____73175 =
                         FStar_Tactics_Embedding.e_result_nbe er  in
                       FStar_TypeChecker_NBETerm.embed uu____73175 cb r  in
                     FStar_Pervasives_Native.Some uu____73174)
  
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
              let uu____73262 =
                extract_3_nbe cb ea eb
                  FStar_Tactics_Embedding.e_proofstate_nbe args
                 in
              FStar_Util.bind_opt uu____73262
                (fun uu____73283  ->
                   match uu____73283 with
                   | (a,b,ps) ->
                       let r =
                         let uu____73298 = t a b  in
                         FStar_Tactics_Basic.run_safe uu____73298 ps  in
                       let uu____73301 =
                         let uu____73302 =
                           FStar_Tactics_Embedding.e_result_nbe er  in
                         FStar_TypeChecker_NBETerm.embed uu____73302 cb r  in
                       FStar_Pervasives_Native.Some uu____73301)
  
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
                let uu____73408 =
                  extract_4_nbe cb ea eb ec
                    FStar_Tactics_Embedding.e_proofstate_nbe args
                   in
                FStar_Util.bind_opt uu____73408
                  (fun uu____73434  ->
                     match uu____73434 with
                     | (a,b,c,ps) ->
                         let r =
                           let uu____73452 = t a b c  in
                           FStar_Tactics_Basic.run_safe uu____73452 ps  in
                         let uu____73455 =
                           let uu____73456 =
                             FStar_Tactics_Embedding.e_result_nbe er  in
                           FStar_TypeChecker_NBETerm.embed uu____73456 cb r
                            in
                         FStar_Pervasives_Native.Some uu____73455)
  
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
                  let uu____73581 =
                    extract_5_nbe cb ea eb ec ed
                      FStar_Tactics_Embedding.e_proofstate_nbe args
                     in
                  FStar_Util.bind_opt uu____73581
                    (fun uu____73612  ->
                       match uu____73612 with
                       | (a,b,c,d,ps) ->
                           let r =
                             let uu____73633 = t a b c d  in
                             FStar_Tactics_Basic.run_safe uu____73633 ps  in
                           let uu____73636 =
                             let uu____73637 =
                               FStar_Tactics_Embedding.e_result_nbe er  in
                             FStar_TypeChecker_NBETerm.embed uu____73637 cb r
                              in
                           FStar_Pervasives_Native.Some uu____73636)
  
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
                    let uu____73781 =
                      extract_6_nbe cb ea eb ec ed ee
                        FStar_Tactics_Embedding.e_proofstate_nbe args
                       in
                    FStar_Util.bind_opt uu____73781
                      (fun uu____73817  ->
                         match uu____73817 with
                         | (a,b,c,d,e,ps) ->
                             let r =
                               let uu____73841 = t a b c d e  in
                               FStar_Tactics_Basic.run_safe uu____73841 ps
                                in
                             let uu____73844 =
                               let uu____73845 =
                                 FStar_Tactics_Embedding.e_result_nbe er  in
                               FStar_TypeChecker_NBETerm.embed uu____73845 cb
                                 r
                                in
                             FStar_Pervasives_Native.Some uu____73844)
  
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
                      let uu____74008 =
                        extract_7_nbe cb ea eb ec ed ee ef
                          FStar_Tactics_Embedding.e_proofstate_nbe args
                         in
                      FStar_Util.bind_opt uu____74008
                        (fun uu____74049  ->
                           match uu____74049 with
                           | (a,b,c,d,e,f,ps) ->
                               let r =
                                 let uu____74076 = t a b c d e f  in
                                 FStar_Tactics_Basic.run_safe uu____74076 ps
                                  in
                               let uu____74079 =
                                 let uu____74080 =
                                   FStar_Tactics_Embedding.e_result_nbe er
                                    in
                                 FStar_TypeChecker_NBETerm.embed uu____74080
                                   cb r
                                  in
                               FStar_Pervasives_Native.Some uu____74079)
  
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
  'Auu____74118 'Auu____74119 'Auu____74120 'Auu____74121 .
    FStar_Ident.lid ->
      ('Auu____74118 -> 'Auu____74119 -> 'Auu____74120 -> 'Auu____74121) ->
        'Auu____74118 -> 'Auu____74119 -> 'Auu____74120 -> 'Auu____74121
  =
  fun l  ->
    fun f  -> fun psc  -> fun cb  -> fun args  -> let r = f psc cb args  in r
  
let timing_nbe :
  'Auu____74178 'Auu____74179 'Auu____74180 .
    FStar_Ident.lid ->
      ('Auu____74178 -> 'Auu____74179 -> 'Auu____74180) ->
        'Auu____74178 -> 'Auu____74179 -> 'Auu____74180
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
  fun uu____74302  -> FStar_Tactics_Native.list_all () 
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____74310  ->
    let uu____74311 = native_tactics ()  in
    FStar_List.map step_from_native_step uu____74311
  
let rec drop :
  'Auu____74321 .
    Prims.int -> 'Auu____74321 Prims.list -> 'Auu____74321 Prims.list
  =
  fun n1  ->
    fun l  ->
      if n1 = (Prims.parse_int "0")
      then l
      else
        (match l with
         | [] -> failwith "drop: impossible"
         | uu____74350::xs -> drop (n1 - (Prims.parse_int "1")) xs)
  
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
                         let uu____74468 = drop nunivs args  in
                         mk_tactic_nbe_interpretation_1 cb nf nea ner
                           uu____74468)
  
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
                             let uu____74624 = drop nunivs args  in
                             mk_tactic_nbe_interpretation_2 cb nf nea neb ner
                               uu____74624)
  
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
                                 let uu____74818 = drop nunivs args  in
                                 mk_tactic_nbe_interpretation_3 cb nf nea neb
                                   nec ner uu____74818)
  
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
                                     let uu____75050 = drop nunivs args  in
                                     mk_tactic_nbe_interpretation_4 cb nf nea
                                       neb nec ned ner uu____75050)
  
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
                                         let uu____75320 = drop nunivs args
                                            in
                                         mk_tactic_nbe_interpretation_5 cb nf
                                           nea neb nec ned nee ner
                                           uu____75320)
  
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
              let uu____75475 = extract_1 ea ncb args  in
              FStar_Util.bind_opt uu____75475
                (fun a  ->
                   let r = f a  in
                   let uu____75485 =
                     let uu____75486 = FStar_TypeChecker_Cfg.psc_range psc
                        in
                     embed er uu____75486 r ncb  in
                   FStar_Pervasives_Native.Some uu____75485)
  
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
                let uu____75576 = extract_2 ea eb ncb args  in
                FStar_Util.bind_opt uu____75576
                  (fun uu____75594  ->
                     match uu____75594 with
                     | (a,b) ->
                         let r = f a b  in
                         let uu____75604 =
                           let uu____75605 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed er uu____75605 r ncb  in
                         FStar_Pervasives_Native.Some uu____75604)
  
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
            let uu____75665 = extract_1_nbe cb ea args  in
            FStar_Util.bind_opt uu____75665
              (fun a  ->
                 let r = f a  in
                 let uu____75673 = FStar_TypeChecker_NBETerm.embed er cb r
                    in
                 FStar_Pervasives_Native.Some uu____75673)
  
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
              let uu____75750 = extract_2_nbe cb ea eb args  in
              FStar_Util.bind_opt uu____75750
                (fun uu____75766  ->
                   match uu____75766 with
                   | (a,b) ->
                       let r = f a b  in
                       let uu____75776 =
                         FStar_TypeChecker_NBETerm.embed er cb r  in
                       FStar_Pervasives_Native.Some uu____75776)
  
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
                         let uu____75882 = drop nunivs args  in
                         mk_total_nbe_interpretation_1 cb nf nea ner
                           uu____75882)
  
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
                             let uu____76030 = drop nunivs args  in
                             mk_total_nbe_interpretation_2 cb nf nea neb ner
                               uu____76030)
  