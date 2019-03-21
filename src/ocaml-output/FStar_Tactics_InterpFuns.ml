open Prims
let unembed :
  'Auu____62349 .
    'Auu____62349 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____62349 FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  ->
        let uu____62373 = FStar_Syntax_Embeddings.unembed e t  in
        uu____62373 true n1
  
let embed :
  'Auu____62392 .
    'Auu____62392 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____62392 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun rng  ->
      fun t  ->
        fun n1  ->
          let uu____62419 = FStar_Syntax_Embeddings.embed e t  in
          uu____62419 rng FStar_Pervasives_Native.None n1
  
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
        | (a,uu____62462)::[] ->
            let uu____62487 = unembed ea a ncb  in
            FStar_Util.bind_opt uu____62487
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____62492 -> failwith "extract_1: wrong number of arguments"
  
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
          | (a,uu____62548)::(b,uu____62550)::[] ->
              let uu____62591 = unembed ea a ncb  in
              FStar_Util.bind_opt uu____62591
                (fun a1  ->
                   let uu____62601 = unembed eb b ncb  in
                   FStar_Util.bind_opt uu____62601
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____62614 -> failwith "extract_2: wrong number of arguments"
  
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
            | (a,uu____62690)::(b,uu____62692)::(c,uu____62694)::[] ->
                let uu____62751 = unembed ea a ncb  in
                FStar_Util.bind_opt uu____62751
                  (fun a1  ->
                     let uu____62763 = unembed eb b ncb  in
                     FStar_Util.bind_opt uu____62763
                       (fun b1  ->
                          let uu____62775 = unembed ec c ncb  in
                          FStar_Util.bind_opt uu____62775
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____62792 -> failwith "extract_3: wrong number of arguments"
  
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
              | (a,uu____62886)::(b,uu____62888)::(c,uu____62890)::(d,uu____62892)::[]
                  ->
                  let uu____62965 = unembed ea a ncb  in
                  FStar_Util.bind_opt uu____62965
                    (fun a1  ->
                       let uu____62979 = unembed eb b ncb  in
                       FStar_Util.bind_opt uu____62979
                         (fun b1  ->
                            let uu____62993 = unembed ec c ncb  in
                            FStar_Util.bind_opt uu____62993
                              (fun c1  ->
                                 let uu____63007 = unembed ed d ncb  in
                                 FStar_Util.bind_opt uu____63007
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____63028 ->
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
                | (a,uu____63140)::(b,uu____63142)::(c,uu____63144)::
                    (d,uu____63146)::(e,uu____63148)::[] ->
                    let uu____63237 = unembed ea a ncb  in
                    FStar_Util.bind_opt uu____63237
                      (fun a1  ->
                         let uu____63253 = unembed eb b ncb  in
                         FStar_Util.bind_opt uu____63253
                           (fun b1  ->
                              let uu____63269 = unembed ec c ncb  in
                              FStar_Util.bind_opt uu____63269
                                (fun c1  ->
                                   let uu____63285 = unembed ed d ncb  in
                                   FStar_Util.bind_opt uu____63285
                                     (fun d1  ->
                                        let uu____63301 = unembed ee e ncb
                                           in
                                        FStar_Util.bind_opt uu____63301
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____63326 ->
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
                  | (a,uu____63456)::(b,uu____63458)::(c,uu____63460)::
                      (d,uu____63462)::(e,uu____63464)::(f,uu____63466)::[]
                      ->
                      let uu____63571 = unembed ea a ncb  in
                      FStar_Util.bind_opt uu____63571
                        (fun a1  ->
                           let uu____63589 = unembed eb b ncb  in
                           FStar_Util.bind_opt uu____63589
                             (fun b1  ->
                                let uu____63607 = unembed ec c ncb  in
                                FStar_Util.bind_opt uu____63607
                                  (fun c1  ->
                                     let uu____63625 = unembed ed d ncb  in
                                     FStar_Util.bind_opt uu____63625
                                       (fun d1  ->
                                          let uu____63643 = unembed ee e ncb
                                             in
                                          FStar_Util.bind_opt uu____63643
                                            (fun e1  ->
                                               let uu____63661 =
                                                 unembed ef f ncb  in
                                               FStar_Util.bind_opt
                                                 uu____63661
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____63690 ->
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
                    | (a,uu____63838)::(b,uu____63840)::(c,uu____63842)::
                        (d,uu____63844)::(e,uu____63846)::(f,uu____63848)::
                        (g,uu____63850)::[] ->
                        let uu____63971 = unembed ea a ncb  in
                        FStar_Util.bind_opt uu____63971
                          (fun a1  ->
                             let uu____63991 = unembed eb b ncb  in
                             FStar_Util.bind_opt uu____63991
                               (fun b1  ->
                                  let uu____64011 = unembed ec c ncb  in
                                  FStar_Util.bind_opt uu____64011
                                    (fun c1  ->
                                       let uu____64031 = unembed ed d ncb  in
                                       FStar_Util.bind_opt uu____64031
                                         (fun d1  ->
                                            let uu____64051 =
                                              unembed ee e ncb  in
                                            FStar_Util.bind_opt uu____64051
                                              (fun e1  ->
                                                 let uu____64071 =
                                                   unembed ef f ncb  in
                                                 FStar_Util.bind_opt
                                                   uu____64071
                                                   (fun f1  ->
                                                      let uu____64091 =
                                                        unembed eg g ncb  in
                                                      FStar_Util.bind_opt
                                                        uu____64091
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____64124 ->
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
                                  | (a1,uu____64386)::(a2,uu____64388)::
                                      (a3,uu____64390)::(a4,uu____64392)::
                                      (a5,uu____64394)::(a6,uu____64396)::
                                      (a7,uu____64398)::(a8,uu____64400)::
                                      (a9,uu____64402)::(a10,uu____64404)::
                                      (a11,uu____64406)::(a12,uu____64408)::
                                      (a13,uu____64410)::(a14,uu____64412)::[]
                                      ->
                                      let uu____64645 = unembed e_t1 a1 ncb
                                         in
                                      FStar_Util.bind_opt uu____64645
                                        (fun a15  ->
                                           let uu____64679 =
                                             unembed e_t2 a2 ncb  in
                                           FStar_Util.bind_opt uu____64679
                                             (fun a21  ->
                                                let uu____64713 =
                                                  unembed e_t3 a3 ncb  in
                                                FStar_Util.bind_opt
                                                  uu____64713
                                                  (fun a31  ->
                                                     let uu____64747 =
                                                       unembed e_t4 a4 ncb
                                                        in
                                                     FStar_Util.bind_opt
                                                       uu____64747
                                                       (fun a41  ->
                                                          let uu____64781 =
                                                            unembed e_t5 a5
                                                              ncb
                                                             in
                                                          FStar_Util.bind_opt
                                                            uu____64781
                                                            (fun a51  ->
                                                               let uu____64815
                                                                 =
                                                                 unembed e_t6
                                                                   a6 ncb
                                                                  in
                                                               FStar_Util.bind_opt
                                                                 uu____64815
                                                                 (fun a61  ->
                                                                    let uu____64849
                                                                    =
                                                                    unembed
                                                                    e_t7 a7
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64849
                                                                    (fun a71 
                                                                    ->
                                                                    let uu____64883
                                                                    =
                                                                    unembed
                                                                    e_t8 a8
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64883
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____64917
                                                                    =
                                                                    unembed
                                                                    e_t9 a9
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64917
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____64951
                                                                    =
                                                                    unembed
                                                                    e_t10 a10
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64951
                                                                    (fun a101
                                                                     ->
                                                                    let uu____64985
                                                                    =
                                                                    unembed
                                                                    e_t11 a11
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____64985
                                                                    (fun a111
                                                                     ->
                                                                    let uu____65019
                                                                    =
                                                                    unembed
                                                                    e_t12 a12
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____65019
                                                                    (fun a121
                                                                     ->
                                                                    let uu____65053
                                                                    =
                                                                    unembed
                                                                    e_t13 a13
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____65053
                                                                    (fun a131
                                                                     ->
                                                                    let uu____65087
                                                                    =
                                                                    unembed
                                                                    e_t14 a14
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____65087
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
                                  | uu____65148 ->
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
        | (a,uu____65212)::[] ->
            let uu____65221 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
            FStar_Util.bind_opt uu____65221
              (fun a1  -> FStar_Pervasives_Native.Some a1)
        | uu____65226 -> failwith "extract_1_nbe: wrong number of arguments"
  
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
          | (a,uu____65280)::(b,uu____65282)::[] ->
              let uu____65295 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
              FStar_Util.bind_opt uu____65295
                (fun a1  ->
                   let uu____65305 =
                     FStar_TypeChecker_NBETerm.unembed eb cb b  in
                   FStar_Util.bind_opt uu____65305
                     (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
          | uu____65318 ->
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
            | (a,uu____65392)::(b,uu____65394)::(c,uu____65396)::[] ->
                let uu____65413 = FStar_TypeChecker_NBETerm.unembed ea cb a
                   in
                FStar_Util.bind_opt uu____65413
                  (fun a1  ->
                     let uu____65425 =
                       FStar_TypeChecker_NBETerm.unembed eb cb b  in
                     FStar_Util.bind_opt uu____65425
                       (fun b1  ->
                          let uu____65437 =
                            FStar_TypeChecker_NBETerm.unembed ec cb c  in
                          FStar_Util.bind_opt uu____65437
                            (fun c1  ->
                               FStar_Pervasives_Native.Some (a1, b1, c1))))
            | uu____65454 ->
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
              | (a,uu____65546)::(b,uu____65548)::(c,uu____65550)::(d,uu____65552)::[]
                  ->
                  let uu____65573 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____65573
                    (fun a1  ->
                       let uu____65587 =
                         FStar_TypeChecker_NBETerm.unembed eb cb b  in
                       FStar_Util.bind_opt uu____65587
                         (fun b1  ->
                            let uu____65601 =
                              FStar_TypeChecker_NBETerm.unembed ec cb c  in
                            FStar_Util.bind_opt uu____65601
                              (fun c1  ->
                                 let uu____65615 =
                                   FStar_TypeChecker_NBETerm.unembed ed cb d
                                    in
                                 FStar_Util.bind_opt uu____65615
                                   (fun d1  ->
                                      FStar_Pervasives_Native.Some
                                        (a1, b1, c1, d1)))))
              | uu____65636 ->
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
                | (a,uu____65746)::(b,uu____65748)::(c,uu____65750)::
                    (d,uu____65752)::(e,uu____65754)::[] ->
                    let uu____65779 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____65779
                      (fun a1  ->
                         let uu____65795 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____65795
                           (fun b1  ->
                              let uu____65811 =
                                FStar_TypeChecker_NBETerm.unembed ec cb c  in
                              FStar_Util.bind_opt uu____65811
                                (fun c1  ->
                                   let uu____65827 =
                                     FStar_TypeChecker_NBETerm.unembed ed cb
                                       d
                                      in
                                   FStar_Util.bind_opt uu____65827
                                     (fun d1  ->
                                        let uu____65843 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            ee cb e
                                           in
                                        FStar_Util.bind_opt uu____65843
                                          (fun e1  ->
                                             FStar_Pervasives_Native.Some
                                               (a1, b1, c1, d1, e1))))))
                | uu____65868 ->
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
                  | (a,uu____65996)::(b,uu____65998)::(c,uu____66000)::
                      (d,uu____66002)::(e,uu____66004)::(f,uu____66006)::[]
                      ->
                      let uu____66035 =
                        FStar_TypeChecker_NBETerm.unembed ea cb a  in
                      FStar_Util.bind_opt uu____66035
                        (fun a1  ->
                           let uu____66053 =
                             FStar_TypeChecker_NBETerm.unembed eb cb b  in
                           FStar_Util.bind_opt uu____66053
                             (fun b1  ->
                                let uu____66071 =
                                  FStar_TypeChecker_NBETerm.unembed ec cb c
                                   in
                                FStar_Util.bind_opt uu____66071
                                  (fun c1  ->
                                     let uu____66089 =
                                       FStar_TypeChecker_NBETerm.unembed ed
                                         cb d
                                        in
                                     FStar_Util.bind_opt uu____66089
                                       (fun d1  ->
                                          let uu____66107 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              ee cb e
                                             in
                                          FStar_Util.bind_opt uu____66107
                                            (fun e1  ->
                                               let uu____66125 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   ef cb f
                                                  in
                                               FStar_Util.bind_opt
                                                 uu____66125
                                                 (fun f1  ->
                                                    FStar_Pervasives_Native.Some
                                                      (a1, b1, c1, d1, e1,
                                                        f1)))))))
                  | uu____66154 ->
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
                    | (a,uu____66300)::(b,uu____66302)::(c,uu____66304)::
                        (d,uu____66306)::(e,uu____66308)::(f,uu____66310)::
                        (g,uu____66312)::[] ->
                        let uu____66345 =
                          FStar_TypeChecker_NBETerm.unembed ea cb a  in
                        FStar_Util.bind_opt uu____66345
                          (fun a1  ->
                             let uu____66365 =
                               FStar_TypeChecker_NBETerm.unembed eb cb b  in
                             FStar_Util.bind_opt uu____66365
                               (fun b1  ->
                                  let uu____66385 =
                                    FStar_TypeChecker_NBETerm.unembed ec cb c
                                     in
                                  FStar_Util.bind_opt uu____66385
                                    (fun c1  ->
                                       let uu____66405 =
                                         FStar_TypeChecker_NBETerm.unembed ed
                                           cb d
                                          in
                                       FStar_Util.bind_opt uu____66405
                                         (fun d1  ->
                                            let uu____66425 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                ee cb e
                                               in
                                            FStar_Util.bind_opt uu____66425
                                              (fun e1  ->
                                                 let uu____66445 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     ef cb f
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____66445
                                                   (fun f1  ->
                                                      let uu____66465 =
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          eg cb g
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____66465
                                                        (fun g1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (a1, b1, c1, d1,
                                                               e1, f1, g1))))))))
                    | uu____66498 ->
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
              let uu____66586 =
                extract_2 ea FStar_Tactics_Embedding.e_proofstate ncb args
                 in
              FStar_Util.bind_opt uu____66586
                (fun uu____66603  ->
                   match uu____66603 with
                   | (a,ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let r =
                         let uu____66616 = t a  in
                         FStar_Tactics_Basic.run_safe uu____66616 ps1  in
                       let uu____66619 =
                         let uu____66620 =
                           FStar_Tactics_Embedding.e_result er  in
                         let uu____66625 =
                           FStar_TypeChecker_Cfg.psc_range psc  in
                         embed uu____66620 uu____66625 r ncb  in
                       FStar_Pervasives_Native.Some uu____66619)
  
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
                let uu____66717 =
                  extract_3 ea eb FStar_Tactics_Embedding.e_proofstate ncb
                    args
                   in
                FStar_Util.bind_opt uu____66717
                  (fun uu____66739  ->
                     match uu____66739 with
                     | (a,b,ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let r =
                           let uu____66755 = t a b  in
                           FStar_Tactics_Basic.run_safe uu____66755 ps1  in
                         let uu____66758 =
                           let uu____66759 =
                             FStar_Tactics_Embedding.e_result er  in
                           let uu____66764 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed uu____66759 uu____66764 r ncb  in
                         FStar_Pervasives_Native.Some uu____66758)
  
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
                  let uu____66875 =
                    extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                      ncb args
                     in
                  FStar_Util.bind_opt uu____66875
                    (fun uu____66902  ->
                       match uu____66902 with
                       | (a,b,c,ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let r =
                             let uu____66921 = t a b c  in
                             FStar_Tactics_Basic.run_safe uu____66921 ps1  in
                           let uu____66924 =
                             let uu____66925 =
                               FStar_Tactics_Embedding.e_result er  in
                             let uu____66930 =
                               FStar_TypeChecker_Cfg.psc_range psc  in
                             embed uu____66925 uu____66930 r ncb  in
                           FStar_Pervasives_Native.Some uu____66924)
  
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
                    let uu____67060 =
                      extract_5 ea eb ec ed
                        FStar_Tactics_Embedding.e_proofstate ncb args
                       in
                    FStar_Util.bind_opt uu____67060
                      (fun uu____67092  ->
                         match uu____67092 with
                         | (a,b,c,d,ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let r =
                               let uu____67114 = t a b c d  in
                               FStar_Tactics_Basic.run_safe uu____67114 ps1
                                in
                             let uu____67117 =
                               let uu____67118 =
                                 FStar_Tactics_Embedding.e_result er  in
                               let uu____67123 =
                                 FStar_TypeChecker_Cfg.psc_range psc  in
                               embed uu____67118 uu____67123 r ncb  in
                             FStar_Pervasives_Native.Some uu____67117)
  
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
                      let uu____67272 =
                        extract_6 ea eb ec ed ee
                          FStar_Tactics_Embedding.e_proofstate ncb args
                         in
                      FStar_Util.bind_opt uu____67272
                        (fun uu____67309  ->
                           match uu____67309 with
                           | (a,b,c,d,e,ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let r =
                                 let uu____67334 = t a b c d e  in
                                 FStar_Tactics_Basic.run_safe uu____67334 ps1
                                  in
                               let uu____67337 =
                                 let uu____67338 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____67343 =
                                   FStar_TypeChecker_Cfg.psc_range psc  in
                                 embed uu____67338 uu____67343 r ncb  in
                               FStar_Pervasives_Native.Some uu____67337)
  
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
                        let uu____67511 =
                          extract_7 ea eb ec ed ee ef
                            FStar_Tactics_Embedding.e_proofstate ncb args
                           in
                        FStar_Util.bind_opt uu____67511
                          (fun uu____67553  ->
                             match uu____67553 with
                             | (a,b,c,d,e,f,ps) ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 let r =
                                   let uu____67581 = t a b c d e f  in
                                   FStar_Tactics_Basic.run_safe uu____67581
                                     ps1
                                    in
                                 let uu____67584 =
                                   let uu____67585 =
                                     FStar_Tactics_Embedding.e_result er  in
                                   let uu____67590 =
                                     FStar_TypeChecker_Cfg.psc_range psc  in
                                   embed uu____67585 uu____67590 r ncb  in
                                 FStar_Pervasives_Native.Some uu____67584)
  
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
                                      let uu____67891 =
                                        extract_14 e_t1 e_t2 e_t3 e_t4 e_t5
                                          e_t6 e_t7 e_t8 e_t9 e_t10 e_t11
                                          e_t12 e_t13
                                          FStar_Tactics_Embedding.e_proofstate
                                          ncb args
                                         in
                                      FStar_Util.bind_opt uu____67891
                                        (fun uu____67968  ->
                                           match uu____67968 with
                                           | (a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,ps)
                                               ->
                                               let ps1 =
                                                 FStar_Tactics_Types.set_ps_psc
                                                   psc ps
                                                  in
                                               let r =
                                                 let uu____68017 =
                                                   t a1 a2 a3 a4 a5 a6 a7 a8
                                                     a9 a10 a11 a12 a13
                                                    in
                                                 FStar_Tactics_Basic.run_safe
                                                   uu____68017 ps1
                                                  in
                                               let uu____68020 =
                                                 let uu____68021 =
                                                   FStar_Tactics_Embedding.e_result
                                                     er
                                                    in
                                                 let uu____68026 =
                                                   FStar_TypeChecker_Cfg.psc_range
                                                     psc
                                                    in
                                                 embed uu____68021
                                                   uu____68026 r ncb
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____68020)
  
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
            let uu____68090 =
              extract_2_nbe cb ea FStar_Tactics_Embedding.e_proofstate_nbe
                args
               in
            FStar_Util.bind_opt uu____68090
              (fun uu____68106  ->
                 match uu____68106 with
                 | (a,ps) ->
                     let r =
                       let uu____68118 = t a  in
                       FStar_Tactics_Basic.run_safe uu____68118 ps  in
                     let uu____68121 =
                       let uu____68122 =
                         FStar_Tactics_Embedding.e_result_nbe er  in
                       FStar_TypeChecker_NBETerm.embed uu____68122 cb r  in
                     FStar_Pervasives_Native.Some uu____68121)
  
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
              let uu____68209 =
                extract_3_nbe cb ea eb
                  FStar_Tactics_Embedding.e_proofstate_nbe args
                 in
              FStar_Util.bind_opt uu____68209
                (fun uu____68230  ->
                   match uu____68230 with
                   | (a,b,ps) ->
                       let r =
                         let uu____68245 = t a b  in
                         FStar_Tactics_Basic.run_safe uu____68245 ps  in
                       let uu____68248 =
                         let uu____68249 =
                           FStar_Tactics_Embedding.e_result_nbe er  in
                         FStar_TypeChecker_NBETerm.embed uu____68249 cb r  in
                       FStar_Pervasives_Native.Some uu____68248)
  
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
                let uu____68355 =
                  extract_4_nbe cb ea eb ec
                    FStar_Tactics_Embedding.e_proofstate_nbe args
                   in
                FStar_Util.bind_opt uu____68355
                  (fun uu____68381  ->
                     match uu____68381 with
                     | (a,b,c,ps) ->
                         let r =
                           let uu____68399 = t a b c  in
                           FStar_Tactics_Basic.run_safe uu____68399 ps  in
                         let uu____68402 =
                           let uu____68403 =
                             FStar_Tactics_Embedding.e_result_nbe er  in
                           FStar_TypeChecker_NBETerm.embed uu____68403 cb r
                            in
                         FStar_Pervasives_Native.Some uu____68402)
  
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
                  let uu____68528 =
                    extract_5_nbe cb ea eb ec ed
                      FStar_Tactics_Embedding.e_proofstate_nbe args
                     in
                  FStar_Util.bind_opt uu____68528
                    (fun uu____68559  ->
                       match uu____68559 with
                       | (a,b,c,d,ps) ->
                           let r =
                             let uu____68580 = t a b c d  in
                             FStar_Tactics_Basic.run_safe uu____68580 ps  in
                           let uu____68583 =
                             let uu____68584 =
                               FStar_Tactics_Embedding.e_result_nbe er  in
                             FStar_TypeChecker_NBETerm.embed uu____68584 cb r
                              in
                           FStar_Pervasives_Native.Some uu____68583)
  
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
                    let uu____68728 =
                      extract_6_nbe cb ea eb ec ed ee
                        FStar_Tactics_Embedding.e_proofstate_nbe args
                       in
                    FStar_Util.bind_opt uu____68728
                      (fun uu____68764  ->
                         match uu____68764 with
                         | (a,b,c,d,e,ps) ->
                             let r =
                               let uu____68788 = t a b c d e  in
                               FStar_Tactics_Basic.run_safe uu____68788 ps
                                in
                             let uu____68791 =
                               let uu____68792 =
                                 FStar_Tactics_Embedding.e_result_nbe er  in
                               FStar_TypeChecker_NBETerm.embed uu____68792 cb
                                 r
                                in
                             FStar_Pervasives_Native.Some uu____68791)
  
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
                      let uu____68955 =
                        extract_7_nbe cb ea eb ec ed ee ef
                          FStar_Tactics_Embedding.e_proofstate_nbe args
                         in
                      FStar_Util.bind_opt uu____68955
                        (fun uu____68996  ->
                           match uu____68996 with
                           | (a,b,c,d,e,f,ps) ->
                               let r =
                                 let uu____69023 = t a b c d e f  in
                                 FStar_Tactics_Basic.run_safe uu____69023 ps
                                  in
                               let uu____69026 =
                                 let uu____69027 =
                                   FStar_Tactics_Embedding.e_result_nbe er
                                    in
                                 FStar_TypeChecker_NBETerm.embed uu____69027
                                   cb r
                                  in
                               FStar_Pervasives_Native.Some uu____69026)
  
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
  'Auu____69065 'Auu____69066 'Auu____69067 'Auu____69068 .
    FStar_Ident.lid ->
      ('Auu____69065 -> 'Auu____69066 -> 'Auu____69067 -> 'Auu____69068) ->
        'Auu____69065 -> 'Auu____69066 -> 'Auu____69067 -> 'Auu____69068
  =
  fun l  ->
    fun f  -> fun psc  -> fun cb  -> fun args  -> let r = f psc cb args  in r
  
let timing_nbe :
  'Auu____69125 'Auu____69126 'Auu____69127 .
    FStar_Ident.lid ->
      ('Auu____69125 -> 'Auu____69126 -> 'Auu____69127) ->
        'Auu____69125 -> 'Auu____69126 -> 'Auu____69127
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
  fun uu____69247  -> FStar_Tactics_Native.list_all () 
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____69255  ->
    let uu____69256 = native_tactics ()  in
    FStar_List.map step_from_native_step uu____69256
  
let rec drop :
  'Auu____69266 .
    Prims.int -> 'Auu____69266 Prims.list -> 'Auu____69266 Prims.list
  =
  fun n1  ->
    fun l  ->
      if n1 = (Prims.parse_int "0")
      then l
      else
        (match l with
         | [] -> failwith "drop: impossible"
         | uu____69295::xs -> drop (n1 - (Prims.parse_int "1")) xs)
  
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
                         let uu____69413 = drop nunivs args  in
                         mk_tactic_nbe_interpretation_1 cb nf nea ner
                           uu____69413)
  
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
                             let uu____69569 = drop nunivs args  in
                             mk_tactic_nbe_interpretation_2 cb nf nea neb ner
                               uu____69569)
  
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
                                 let uu____69763 = drop nunivs args  in
                                 mk_tactic_nbe_interpretation_3 cb nf nea neb
                                   nec ner uu____69763)
  
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
                                     let uu____69995 = drop nunivs args  in
                                     mk_tactic_nbe_interpretation_4 cb nf nea
                                       neb nec ned ner uu____69995)
  
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
                                         let uu____70265 = drop nunivs args
                                            in
                                         mk_tactic_nbe_interpretation_5 cb nf
                                           nea neb nec ned nee ner
                                           uu____70265)
  
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
              let uu____70416 = extract_1 ea ncb args  in
              FStar_Util.bind_opt uu____70416
                (fun a  ->
                   let r = f a  in
                   let uu____70424 =
                     let uu____70425 = FStar_TypeChecker_Cfg.psc_range psc
                        in
                     embed er uu____70425 r ncb  in
                   FStar_Pervasives_Native.Some uu____70424)
  
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
                let uu____70511 = extract_2 ea eb ncb args  in
                FStar_Util.bind_opt uu____70511
                  (fun uu____70527  ->
                     match uu____70527 with
                     | (a,b) ->
                         let r = f a b  in
                         let uu____70537 =
                           let uu____70538 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           embed er uu____70538 r ncb  in
                         FStar_Pervasives_Native.Some uu____70537)
  
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
            let uu____70596 = extract_1_nbe cb ea args  in
            FStar_Util.bind_opt uu____70596
              (fun a  ->
                 let r = f a  in
                 let uu____70604 = FStar_TypeChecker_NBETerm.embed er cb r
                    in
                 FStar_Pervasives_Native.Some uu____70604)
  
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
              let uu____70681 = extract_2_nbe cb ea eb args  in
              FStar_Util.bind_opt uu____70681
                (fun uu____70697  ->
                   match uu____70697 with
                   | (a,b) ->
                       let r = f a b  in
                       let uu____70707 =
                         FStar_TypeChecker_NBETerm.embed er cb r  in
                       FStar_Pervasives_Native.Some uu____70707)
  
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
                         let uu____70813 = drop nunivs args  in
                         mk_total_nbe_interpretation_1 cb nf nea ner
                           uu____70813)
  
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
                             let uu____70961 = drop nunivs args  in
                             mk_total_nbe_interpretation_2 cb nf nea neb ner
                               uu____70961)
  