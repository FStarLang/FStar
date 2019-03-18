open Prims
let unembed :
  'Auu____62316 .
    'Auu____62316 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____62316 FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  ->
        let uu____62340 = FStar_Syntax_Embeddings.unembed e t  in
        uu____62340 true n1
  
let embed :
  'Auu____62359 .
    'Auu____62359 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____62359 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun rng  ->
      fun t  ->
        fun n1  ->
          let uu____62386 = FStar_Syntax_Embeddings.embed e t  in
          uu____62386 rng FStar_Pervasives_Native.None n1
  
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
        | (a,uu____62429)::[] ->
            let uu____62454 = unembed ea a ncb  in
            FStar_Util.bind_opt uu____62454
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____62459 -> failwith "extract_1: wrong number of arguments"
  
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
          | (a,uu____62515)::(b,uu____62517)::[] ->
              let uu____62558 = unembed ea a ncb  in
              FStar_Util.bind_opt uu____62558
                (fun a1  ->
                   let uu____62568 = unembed eb b ncb  in
                   FStar_Util.bind_opt uu____62568
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____62581 -> failwith "extract_2: wrong number of arguments"
  
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
            | (a,uu____62657)::(b,uu____62659)::(c,uu____62661)::[] ->
                let uu____62718 = unembed ea a ncb  in
                FStar_Util.bind_opt uu____62718
                  (fun a1  ->
                     let uu____62730 = unembed eb b ncb  in
                     FStar_Util.bind_opt uu____62730
                       (fun b1  ->
                          let uu____62742 = unembed ec c ncb  in
                          FStar_Util.bind_opt uu____62742
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____62759 -> failwith "extract_3: wrong number of arguments"
  
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
              | (a,uu____62853)::(b,uu____62855)::(c,uu____62857)::(d,uu____62859)::[]
                  ->
                  let uu____62932 = unembed ea a ncb  in
                  FStar_Util.bind_opt uu____62932
                    (fun a1  ->
                       let uu____62946 = unembed eb b ncb  in
                       FStar_Util.bind_opt uu____62946
                         (fun b1  ->
                            let uu____62960 = unembed ec c ncb  in
                            FStar_Util.bind_opt uu____62960
                              (fun c1  ->
                                 let uu____62974 = unembed ed d ncb  in
                                 FStar_Util.bind_opt uu____62974
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____62995 ->
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
                | (a,uu____63107)::(b,uu____63109)::(c,uu____63111)::
                    (d,uu____63113)::(e,uu____63115)::[] ->
                    let uu____63204 = unembed ea a ncb  in
                    FStar_Util.bind_opt uu____63204
                      (fun a1  ->
                         let uu____63220 = unembed eb b ncb  in
                         FStar_Util.bind_opt uu____63220
                           (fun b1  ->
                              let uu____63236 = unembed ec c ncb  in
                              FStar_Util.bind_opt uu____63236
                                (fun c1  ->
                                   let uu____63252 = unembed ed d ncb  in
                                   FStar_Util.bind_opt uu____63252
                                     (fun d1  ->
                                        let uu____63268 = unembed ee e ncb
                                           in
                                        FStar_Util.bind_opt uu____63268
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____63293 ->
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
                  | (a,uu____63423)::(b,uu____63425)::(c,uu____63427)::
                      (d,uu____63429)::(e,uu____63431)::(f,uu____63433)::[]
                      ->
                      let uu____63538 = unembed ea a ncb  in
                      FStar_Util.bind_opt uu____63538
                        (fun a1  ->
                           let uu____63556 = unembed eb b ncb  in
                           FStar_Util.bind_opt uu____63556
                             (fun b1  ->
                                let uu____63574 = unembed ec c ncb  in
                                FStar_Util.bind_opt uu____63574
                                  (fun c1  ->
                                     let uu____63592 = unembed ed d ncb  in
                                     FStar_Util.bind_opt uu____63592
                                       (fun d1  ->
                                          let uu____63610 = unembed ee e ncb
                                             in
                                          FStar_Util.bind_opt uu____63610
                                            (fun e1  ->
                                               let uu____63628 =
                                                 unembed ef f ncb  in
                                               FStar_Util.bind_opt
                                                 uu____63628
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____63657 ->
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
                    | (a,uu____63805)::(b,uu____63807)::(c,uu____63809)::
                        (d,uu____63811)::(e,uu____63813)::(f,uu____63815)::
                        (g,uu____63817)::[] ->
                        let uu____63938 = unembed ea a ncb  in
                        FStar_Util.bind_opt uu____63938
                          (fun a1  ->
                             let uu____63958 = unembed eb b ncb  in
                             FStar_Util.bind_opt uu____63958
                               (fun b1  ->
                                  let uu____63978 = unembed ec c ncb  in
                                  FStar_Util.bind_opt uu____63978
                                    (fun c1  ->
                                       let uu____63998 = unembed ed d ncb  in
                                       FStar_Util.bind_opt uu____63998
                                         (fun d1  ->
                                            let uu____64018 =
                                              unembed ee e ncb  in
                                            FStar_Util.bind_opt uu____64018
                                              (fun e1  ->
                                                 let uu____64038 =
                                                   unembed ef f ncb  in
                                                 FStar_Util.bind_opt
                                                   uu____64038
                                                   (fun f1  ->
                                                      let uu____64058 =
                                                        unembed eg g ncb  in
                                                      FStar_Util.bind_opt
                                                        uu____64058
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____64091 ->
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
                                  | (a1,uu____64353)::(a2,uu____64355)::
                                      (a3,uu____64357)::(a4,uu____64359)::
                                      (a5,uu____64361)::(a6,uu____64363)::
                                      (a7,uu____64365)::(a8,uu____64367)::
                                      (a9,uu____64369)::(a10,uu____64371)::
                                      (a11,uu____64373)::(a12,uu____64375)::
                                      (a13,uu____64377)::(a14,uu____64379)::[]
                                      ->
                                      let uu____64612 = unembed e_t1 a1 ncb
                                         in
                                      FStar_Util.bind_opt uu____64612
                                        (fun a15  ->
                                           let uu____64646 =
                                             unembed e_t2 a2 ncb  in
                                           FStar_Util.bind_opt uu____64646
                                             (fun a21  ->
                                                let uu____64680 =
                                                  unembed e_t3 a3 ncb  in
                                                FStar_Util.bind_opt
                                                  uu____64680
                                                  (fun a31  ->
                                                     let uu____64714 =
                                                       unembed e_t4 a4 ncb
                                                        in
                                                     FStar_Util.bind_opt
                                                       uu____64714
                                                       (fun a41  ->
                                                          let uu____64748 =
                                                            unembed e_t5 a5
                                                              ncb
                                                             in
                                                          FStar_Util.bind_opt
                                                            uu____64748
                                                            (fun a51  ->
                                                               let uu____64782
                                                                 =
                                                                 unembed e_t6
                                                                   a6 ncb
                                                                  in
                                                               FStar_Util.bind_opt
                                                                 uu____64782
                                                                 (fun a61  ->
                                                                    let uu____64816
                                                                    =
                                                                    unembed
                                                                    e_t7 a7
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64816
                                                                    (fun a71 
                                                                    ->
                                                                    let uu____64850
                                                                    =
                                                                    unembed
                                                                    e_t8 a8
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64850
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____64884
                                                                    =
                                                                    unembed
                                                                    e_t9 a9
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64884
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____64918
                                                                    =
                                                                    unembed
                                                                    e_t10 a10
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64918
                                                                    (fun a101
                                                                     ->
                                                                    let uu____64952
                                                                    =
                                                                    unembed
                                                                    e_t11 a11
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64952
                                                                    (fun a111
                                                                     ->
                                                                    let uu____64986
                                                                    =
                                                                    unembed
                                                                    e_t12 a12
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64986
                                                                    (fun a121
                                                                     ->
                                                                    let uu____65020
                                                                    =
                                                                    unembed
                                                                    e_t13 a13
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____65020
                                                                    (fun a131
                                                                     ->
                                                                    let uu____65054
                                                                    =
                                                                    unembed
                                                                    e_t14 a14
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____65054
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
                                  | uu____65115 ->
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
        | (a,uu____65179)::[] ->
            let uu____65188 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
            FStar_Util.bind_opt uu____65188
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____65193 -> failwith "extract_1_nbe: wrong number of arguments"
  
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
          | (a,uu____65247)::(b,uu____65249)::[] ->
              let uu____65262 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
              FStar_Util.bind_opt uu____65262
                (fun a1  ->
                   let uu____65272 =
                     FStar_TypeChecker_NBETerm.unembed eb cb b  in
                   FStar_Util.bind_opt uu____65272
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____65285 ->
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
            | (a,uu____65359)::(b,uu____65361)::(c,uu____65363)::[] ->
                let uu____65380 = FStar_TypeChecker_NBETerm.unembed ea cb a
                   in
                FStar_Util.bind_opt uu____65380
                  (fun a1  ->
                     let uu____65392 =
                       FStar_TypeChecker_NBETerm.unembed eb cb b  in
                     FStar_Util.bind_opt uu____65392
                       (fun b1  ->
                          let uu____65404 =
                            FStar_TypeChecker_NBETerm.unembed ec cb c  in
                          FStar_Util.bind_opt uu____65404
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____65421 ->
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
              | (a,uu____65513)::(b,uu____65515)::(c,uu____65517)::(d,uu____65519)::[]
                  ->
                  let uu____65540 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____65540
                    (fun a1  ->
                       let uu____65554 =
                         FStar_TypeChecker_NBETerm.unembed eb cb b  in
                       FStar_Util.bind_opt uu____65554
                         (fun b1  ->
                            let uu____65568 =
                              FStar_TypeChecker_NBETerm.unembed ec cb c  in
                            FStar_Util.bind_opt uu____65568
                              (fun c1  ->
                                 let uu____65582 =
                                   FStar_TypeChecker_NBETerm.unembed ed cb d
                                    in
                                 FStar_Util.bind_opt uu____65582
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____65603 ->
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
                | (a,uu____65713)::(b,uu____65715)::(c,uu____65717)::
                    (d,uu____65719)::(e,uu____65721)::[] ->
                    let uu____65746 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____65746
                      (fun a1  ->
                         let uu____65762 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____65762
                           (fun b1  ->
                              let uu____65778 =
                                FStar_TypeChecker_NBETerm.unembed ec cb c  in
                              FStar_Util.bind_opt uu____65778
                                (fun c1  ->
                                   let uu____65794 =
                                     FStar_TypeChecker_NBETerm.unembed ed cb
                                       d
                                      in
                                   FStar_Util.bind_opt uu____65794
                                     (fun d1  ->
                                        let uu____65810 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            ee cb e
                                           in
                                        FStar_Util.bind_opt uu____65810
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____65835 ->
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
                  | (a,uu____65963)::(b,uu____65965)::(c,uu____65967)::
                      (d,uu____65969)::(e,uu____65971)::(f,uu____65973)::[]
                      ->
                      let uu____66002 =
                        FStar_TypeChecker_NBETerm.unembed ea cb a  in
                      FStar_Util.bind_opt uu____66002
                        (fun a1  ->
                           let uu____66020 =
                             FStar_TypeChecker_NBETerm.unembed eb cb b  in
                           FStar_Util.bind_opt uu____66020
                             (fun b1  ->
                                let uu____66038 =
                                  FStar_TypeChecker_NBETerm.unembed ec cb c
                                   in
                                FStar_Util.bind_opt uu____66038
                                  (fun c1  ->
                                     let uu____66056 =
                                       FStar_TypeChecker_NBETerm.unembed ed
                                         cb d
                                        in
                                     FStar_Util.bind_opt uu____66056
                                       (fun d1  ->
                                          let uu____66074 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              ee cb e
                                             in
                                          FStar_Util.bind_opt uu____66074
                                            (fun e1  ->
                                               let uu____66092 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   ef cb f
                                                  in
                                               FStar_Util.bind_opt
                                                 uu____66092
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____66121 ->
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
                    | (a,uu____66267)::(b,uu____66269)::(c,uu____66271)::
                        (d,uu____66273)::(e,uu____66275)::(f,uu____66277)::
                        (g,uu____66279)::[] ->
                        let uu____66312 =
                          FStar_TypeChecker_NBETerm.unembed ea cb a  in
                        FStar_Util.bind_opt uu____66312
                          (fun a1  ->
                             let uu____66332 =
                               FStar_TypeChecker_NBETerm.unembed eb cb b  in
                             FStar_Util.bind_opt uu____66332
                               (fun b1  ->
                                  let uu____66352 =
                                    FStar_TypeChecker_NBETerm.unembed ec cb c
                                     in
                                  FStar_Util.bind_opt uu____66352
                                    (fun c1  ->
                                       let uu____66372 =
                                         FStar_TypeChecker_NBETerm.unembed ed
                                           cb d
                                          in
                                       FStar_Util.bind_opt uu____66372
                                         (fun d1  ->
                                            let uu____66392 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                ee cb e
                                               in
                                            FStar_Util.bind_opt uu____66392
                                              (fun e1  ->
                                                 let uu____66412 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     ef cb f
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____66412
                                                   (fun f1  ->
                                                      let uu____66432 =
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          eg cb g
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____66432
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____66465 ->
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
              let uu____66553 =
                extract_2 ea FStar_Tactics_Embedding.e_proofstate ncb args
                 in
              FStar_Util.bind_opt uu____66553
                (fun uu____66570  ->
                   match uu____66570 with
                   | (a,ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let r =
                         let uu____66583 = t a  in
                         FStar_Tactics_Basic.run_safe uu____66583 ps1  in
                       let uu____66586 =
                         let uu____66587 =
                           FStar_Tactics_Embedding.e_result er  in
                         let uu____66592 =
                           FStar_TypeChecker_Cfg.psc_range psc  in
                         embed uu____66587 uu____66592 r ncb  in
                       FStar_Pervasives_Native.Some uu____66586)
  
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
                let uu____66684 =
                  extract_3 ea eb FStar_Tactics_Embedding.e_proofstate ncb
                    args
                   in
                FStar_Util.bind_opt uu____66684
                  (fun uu____66706  ->
                     match uu____66706 with
                     | (a,b,ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let r =
                           let uu____66722 = t a b  in
                           FStar_Tactics_Basic.run_safe uu____66722 ps1  in
                         let uu____66725 =
                           let uu____66726 =
                             FStar_Tactics_Embedding.e_result er  in
                           let uu____66731 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed uu____66726 uu____66731 r ncb  in
                         FStar_Pervasives_Native.Some uu____66725)
  
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
                  let uu____66842 =
                    extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                      ncb args
                     in
                  FStar_Util.bind_opt uu____66842
                    (fun uu____66869  ->
                       match uu____66869 with
                       | (a,b,c,ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let r =
                             let uu____66888 = t a b c  in
                             FStar_Tactics_Basic.run_safe uu____66888 ps1  in
                           let uu____66891 =
                             let uu____66892 =
                               FStar_Tactics_Embedding.e_result er  in
                             let uu____66897 =
                               FStar_TypeChecker_Cfg.psc_range psc  in
                             embed uu____66892 uu____66897 r ncb  in
                           FStar_Pervasives_Native.Some uu____66891)
  
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
                    let uu____67027 =
                      extract_5 ea eb ec ed
                        FStar_Tactics_Embedding.e_proofstate ncb args
                       in
                    FStar_Util.bind_opt uu____67027
                      (fun uu____67059  ->
                         match uu____67059 with
                         | (a,b,c,d,ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let r =
                               let uu____67081 = t a b c d  in
                               FStar_Tactics_Basic.run_safe uu____67081 ps1
                                in
                             let uu____67084 =
                               let uu____67085 =
                                 FStar_Tactics_Embedding.e_result er  in
                               let uu____67090 =
                                 FStar_TypeChecker_Cfg.psc_range psc  in
                               embed uu____67085 uu____67090 r ncb  in
                             FStar_Pervasives_Native.Some uu____67084)
  
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
                      let uu____67239 =
                        extract_6 ea eb ec ed ee
                          FStar_Tactics_Embedding.e_proofstate ncb args
                         in
                      FStar_Util.bind_opt uu____67239
                        (fun uu____67276  ->
                           match uu____67276 with
                           | (a,b,c,d,e,ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let r =
                                 let uu____67301 = t a b c d e  in
                                 FStar_Tactics_Basic.run_safe uu____67301 ps1
                                  in
                               let uu____67304 =
                                 let uu____67305 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____67310 =
                                   FStar_TypeChecker_Cfg.psc_range psc  in
                                 embed uu____67305 uu____67310 r ncb  in
                               FStar_Pervasives_Native.Some uu____67304)
  
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
                        let uu____67478 =
                          extract_7 ea eb ec ed ee ef
                            FStar_Tactics_Embedding.e_proofstate ncb args
                           in
                        FStar_Util.bind_opt uu____67478
                          (fun uu____67520  ->
                             match uu____67520 with
                             | (a,b,c,d,e,f,ps) ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 let r =
                                   let uu____67548 = t a b c d e f  in
                                   FStar_Tactics_Basic.run_safe uu____67548
                                     ps1
                                    in
                                 let uu____67551 =
                                   let uu____67552 =
                                     FStar_Tactics_Embedding.e_result er  in
                                   let uu____67557 =
                                     FStar_TypeChecker_Cfg.psc_range psc  in
                                   embed uu____67552 uu____67557 r ncb  in
                                 FStar_Pervasives_Native.Some uu____67551)
  
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
                                      let uu____67858 =
                                        extract_14 e_t1 e_t2 e_t3 e_t4 e_t5
                                          e_t6 e_t7 e_t8 e_t9 e_t10 e_t11
                                          e_t12 e_t13
                                          FStar_Tactics_Embedding.e_proofstate
                                          ncb args
                                         in
                                      FStar_Util.bind_opt uu____67858
                                        (fun uu____67935  ->
                                           match uu____67935 with
                                           | (a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,ps)
                                               ->
                                               let ps1 =
                                                 FStar_Tactics_Types.set_ps_psc
                                                   psc ps
                                                  in
                                               let r =
                                                 let uu____67984 =
                                                   t a1 a2 a3 a4 a5 a6 a7 a8
                                                     a9 a10 a11 a12 a13
                                                    in
                                                 FStar_Tactics_Basic.run_safe
                                                   uu____67984 ps1
                                                  in
                                               let uu____67987 =
                                                 let uu____67988 =
                                                   FStar_Tactics_Embedding.e_result
                                                     er
                                                    in
                                                 let uu____67993 =
                                                   FStar_TypeChecker_Cfg.psc_range
                                                     psc
                                                    in
                                                 embed uu____67988
                                                   uu____67993 r ncb
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____67987)
  
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
            let uu____68057 =
              extract_2_nbe cb ea FStar_Tactics_Embedding.e_proofstate_nbe
                args
               in
            FStar_Util.bind_opt uu____68057
              (fun uu____68073  ->
                 match uu____68073 with
                 | (a,ps) ->
                     let r =
                       let uu____68085 = t a  in
                       FStar_Tactics_Basic.run_safe uu____68085 ps  in
                     let uu____68088 =
                       let uu____68089 =
                         FStar_Tactics_Embedding.e_result_nbe er  in
                       FStar_TypeChecker_NBETerm.embed uu____68089 cb r  in
                     FStar_Pervasives_Native.Some uu____68088)
  
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
              let uu____68176 =
                extract_3_nbe cb ea eb
                  FStar_Tactics_Embedding.e_proofstate_nbe args
                 in
              FStar_Util.bind_opt uu____68176
                (fun uu____68197  ->
                   match uu____68197 with
                   | (a,b,ps) ->
                       let r =
                         let uu____68212 = t a b  in
                         FStar_Tactics_Basic.run_safe uu____68212 ps  in
                       let uu____68215 =
                         let uu____68216 =
                           FStar_Tactics_Embedding.e_result_nbe er  in
                         FStar_TypeChecker_NBETerm.embed uu____68216 cb r  in
                       FStar_Pervasives_Native.Some uu____68215)
  
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
                let uu____68322 =
                  extract_4_nbe cb ea eb ec
                    FStar_Tactics_Embedding.e_proofstate_nbe args
                   in
                FStar_Util.bind_opt uu____68322
                  (fun uu____68348  ->
                     match uu____68348 with
                     | (a,b,c,ps) ->
                         let r =
                           let uu____68366 = t a b c  in
                           FStar_Tactics_Basic.run_safe uu____68366 ps  in
                         let uu____68369 =
                           let uu____68370 =
                             FStar_Tactics_Embedding.e_result_nbe er  in
                           FStar_TypeChecker_NBETerm.embed uu____68370 cb r
                            in
                         FStar_Pervasives_Native.Some uu____68369)
  
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
                  let uu____68495 =
                    extract_5_nbe cb ea eb ec ed
                      FStar_Tactics_Embedding.e_proofstate_nbe args
                     in
                  FStar_Util.bind_opt uu____68495
                    (fun uu____68526  ->
                       match uu____68526 with
                       | (a,b,c,d,ps) ->
                           let r =
                             let uu____68547 = t a b c d  in
                             FStar_Tactics_Basic.run_safe uu____68547 ps  in
                           let uu____68550 =
                             let uu____68551 =
                               FStar_Tactics_Embedding.e_result_nbe er  in
                             FStar_TypeChecker_NBETerm.embed uu____68551 cb r
                              in
                           FStar_Pervasives_Native.Some uu____68550)
  
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
                    let uu____68695 =
                      extract_6_nbe cb ea eb ec ed ee
                        FStar_Tactics_Embedding.e_proofstate_nbe args
                       in
                    FStar_Util.bind_opt uu____68695
                      (fun uu____68731  ->
                         match uu____68731 with
                         | (a,b,c,d,e,ps) ->
                             let r =
                               let uu____68755 = t a b c d e  in
                               FStar_Tactics_Basic.run_safe uu____68755 ps
                                in
                             let uu____68758 =
                               let uu____68759 =
                                 FStar_Tactics_Embedding.e_result_nbe er  in
                               FStar_TypeChecker_NBETerm.embed uu____68759 cb
                                 r
                                in
                             FStar_Pervasives_Native.Some uu____68758)
  
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
                      let uu____68922 =
                        extract_7_nbe cb ea eb ec ed ee ef
                          FStar_Tactics_Embedding.e_proofstate_nbe args
                         in
                      FStar_Util.bind_opt uu____68922
                        (fun uu____68963  ->
                           match uu____68963 with
                           | (a,b,c,d,e,f,ps) ->
                               let r =
                                 let uu____68990 = t a b c d e f  in
                                 FStar_Tactics_Basic.run_safe uu____68990 ps
                                  in
                               let uu____68993 =
                                 let uu____68994 =
                                   FStar_Tactics_Embedding.e_result_nbe er
                                    in
                                 FStar_TypeChecker_NBETerm.embed uu____68994
                                   cb r
                                  in
                               FStar_Pervasives_Native.Some uu____68993)
  
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
  'Auu____69032 'Auu____69033 'Auu____69034 'Auu____69035 .
    FStar_Ident.lid ->
      ('Auu____69032 -> 'Auu____69033 -> 'Auu____69034 -> 'Auu____69035) ->
        'Auu____69032 -> 'Auu____69033 -> 'Auu____69034 -> 'Auu____69035
  =
  fun l  ->
    fun f  -> fun psc  -> fun cb  -> fun args  -> let r = f psc cb args  in r
  
let timing_nbe :
  'Auu____69092 'Auu____69093 'Auu____69094 .
    FStar_Ident.lid ->
      ('Auu____69092 -> 'Auu____69093 -> 'Auu____69094) ->
        'Auu____69092 -> 'Auu____69093 -> 'Auu____69094
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
  fun uu____69214  -> FStar_Tactics_Native.list_all () 
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____69222  ->
    let uu____69223 = native_tactics ()  in
    FStar_List.map step_from_native_step uu____69223
  
let rec drop :
  'Auu____69233 .
    Prims.int -> 'Auu____69233 Prims.list -> 'Auu____69233 Prims.list
  =
  fun n1  ->
    fun l  ->
      if n1 = (Prims.parse_int "0")
      then l
      else
        (match l with
         | [] -> failwith "drop: impossible"
         | uu____69262::xs -> drop (n1 - (Prims.parse_int "1")) xs)
  
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
                         let uu____69380 = drop nunivs args  in
                         mk_tactic_nbe_interpretation_1 cb nf nea ner
                           uu____69380)
  
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
                             let uu____69536 = drop nunivs args  in
                             mk_tactic_nbe_interpretation_2 cb nf nea neb ner
                               uu____69536)
  
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
                                 let uu____69730 = drop nunivs args  in
                                 mk_tactic_nbe_interpretation_3 cb nf nea neb
                                   nec ner uu____69730)
  
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
                                     let uu____69962 = drop nunivs args  in
                                     mk_tactic_nbe_interpretation_4 cb nf nea
                                       neb nec ned ner uu____69962)
  
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
                                         let uu____70232 = drop nunivs args
                                            in
                                         mk_tactic_nbe_interpretation_5 cb nf
                                           nea neb nec ned nee ner
                                           uu____70232)
  
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
              let uu____70383 = extract_1 ea ncb args  in
              FStar_Util.bind_opt uu____70383
                (fun a  ->
                   let r = f a  in
                   let uu____70391 =
                     let uu____70392 = FStar_TypeChecker_Cfg.psc_range psc
                        in
                     embed er uu____70392 r ncb  in
                   FStar_Pervasives_Native.Some uu____70391)
  
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
                let uu____70478 = extract_2 ea eb ncb args  in
                FStar_Util.bind_opt uu____70478
                  (fun uu____70494  ->
                     match uu____70494 with
                     | (a,b) ->
                         let r = f a b  in
                         let uu____70504 =
                           let uu____70505 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed er uu____70505 r ncb  in
                         FStar_Pervasives_Native.Some uu____70504)
  
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
            let uu____70563 = extract_1_nbe cb ea args  in
            FStar_Util.bind_opt uu____70563
              (fun a  ->
                 let r = f a  in
                 let uu____70571 = FStar_TypeChecker_NBETerm.embed er cb r
                    in
                 FStar_Pervasives_Native.Some uu____70571)
  
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
              let uu____70648 = extract_2_nbe cb ea eb args  in
              FStar_Util.bind_opt uu____70648
                (fun uu____70664  ->
                   match uu____70664 with
                   | (a,b) ->
                       let r = f a b  in
                       let uu____70674 =
                         FStar_TypeChecker_NBETerm.embed er cb r  in
                       FStar_Pervasives_Native.Some uu____70674)
  
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
                         let uu____70780 = drop nunivs args  in
                         mk_total_nbe_interpretation_1 cb nf nea ner
                           uu____70780)
  
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
                             let uu____70928 = drop nunivs args  in
                             mk_total_nbe_interpretation_2 cb nf nea neb ner
                               uu____70928)
  