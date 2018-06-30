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
            let uu____1698 =
              extract_2 ea FStar_Tactics_Embedding.e_proofstate args  in
            FStar_Util.bind_opt uu____1698
              (fun uu____1715  ->
                 match uu____1715 with
                 | (a,ps) ->
                     let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                     let r =
                       let uu____1728 = t a  in
                       FStar_Tactics_Basic.run_safe uu____1728 ps1  in
                     let uu____1731 =
                       let uu____1732 = FStar_Tactics_Embedding.e_result er
                          in
                       let uu____1737 = FStar_TypeChecker_Cfg.psc_range psc
                          in
                       FStar_Syntax_Embeddings.embed uu____1732 uu____1737 r
                        in
                     FStar_Pervasives_Native.Some uu____1731)
  
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
              let uu____1819 =
                extract_3 ea eb FStar_Tactics_Embedding.e_proofstate args  in
              FStar_Util.bind_opt uu____1819
                (fun uu____1841  ->
                   match uu____1841 with
                   | (a,b,ps) ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       let r =
                         let uu____1857 = t a b  in
                         FStar_Tactics_Basic.run_safe uu____1857 ps1  in
                       let uu____1860 =
                         let uu____1861 = FStar_Tactics_Embedding.e_result er
                            in
                         let uu____1866 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         FStar_Syntax_Embeddings.embed uu____1861 uu____1866
                           r
                          in
                       FStar_Pervasives_Native.Some uu____1860)
  
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
                let uu____1967 =
                  extract_4 ea eb ec FStar_Tactics_Embedding.e_proofstate
                    args
                   in
                FStar_Util.bind_opt uu____1967
                  (fun uu____1994  ->
                     match uu____1994 with
                     | (a,b,c,ps) ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         let r =
                           let uu____2013 = t a b c  in
                           FStar_Tactics_Basic.run_safe uu____2013 ps1  in
                         let uu____2016 =
                           let uu____2017 =
                             FStar_Tactics_Embedding.e_result er  in
                           let uu____2022 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           FStar_Syntax_Embeddings.embed uu____2017
                             uu____2022 r
                            in
                         FStar_Pervasives_Native.Some uu____2016)
  
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
                  let uu____2142 =
                    extract_5 ea eb ec ed
                      FStar_Tactics_Embedding.e_proofstate args
                     in
                  FStar_Util.bind_opt uu____2142
                    (fun uu____2174  ->
                       match uu____2174 with
                       | (a,b,c,d,ps) ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           let r =
                             let uu____2196 = t a b c d  in
                             FStar_Tactics_Basic.run_safe uu____2196 ps1  in
                           let uu____2199 =
                             let uu____2200 =
                               FStar_Tactics_Embedding.e_result er  in
                             let uu____2205 =
                               FStar_TypeChecker_Cfg.psc_range psc  in
                             FStar_Syntax_Embeddings.embed uu____2200
                               uu____2205 r
                              in
                           FStar_Pervasives_Native.Some uu____2199)
  
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
                    let uu____2344 =
                      extract_6 ea eb ec ed ee
                        FStar_Tactics_Embedding.e_proofstate args
                       in
                    FStar_Util.bind_opt uu____2344
                      (fun uu____2381  ->
                         match uu____2381 with
                         | (a,b,c,d,e,ps) ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             let r =
                               let uu____2406 = t a b c d e  in
                               FStar_Tactics_Basic.run_safe uu____2406 ps1
                                in
                             let uu____2409 =
                               let uu____2410 =
                                 FStar_Tactics_Embedding.e_result er  in
                               let uu____2415 =
                                 FStar_TypeChecker_Cfg.psc_range psc  in
                               FStar_Syntax_Embeddings.embed uu____2410
                                 uu____2415 r
                                in
                             FStar_Pervasives_Native.Some uu____2409)
  
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
                      let uu____2573 =
                        extract_7 ea eb ec ed ee ef
                          FStar_Tactics_Embedding.e_proofstate args
                         in
                      FStar_Util.bind_opt uu____2573
                        (fun uu____2615  ->
                           match uu____2615 with
                           | (a,b,c,d,e,f,ps) ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               let r =
                                 let uu____2643 = t a b c d e f  in
                                 FStar_Tactics_Basic.run_safe uu____2643 ps1
                                  in
                               let uu____2646 =
                                 let uu____2647 =
                                   FStar_Tactics_Embedding.e_result er  in
                                 let uu____2652 =
                                   FStar_TypeChecker_Cfg.psc_range psc  in
                                 FStar_Syntax_Embeddings.embed uu____2647
                                   uu____2652 r
                                  in
                               FStar_Pervasives_Native.Some uu____2646)
  
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
          -> FStar_TypeChecker_Cfg.primitive_step)
  =
  fun nm  ->
    fun arity  ->
      fun nunivs  ->
        fun interpretation  ->
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
            FStar_TypeChecker_Cfg.interpretation = interpretation;
            FStar_TypeChecker_Cfg.interpretation_nbe =
              (FStar_TypeChecker_NBETerm.dummy_interp nm1)
          }
  
let (native_tactics : FStar_Tactics_Native.native_primitive_step Prims.list)
  = FStar_Tactics_Native.list_all () 
let (native_tactics_steps : FStar_TypeChecker_Cfg.primitive_step Prims.list)
  = FStar_List.map step_from_native_step native_tactics 
let mktac1 :
  'a 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun er  ->
            mk name (Prims.parse_int "2") nunivs
              (mk_tactic_interpretation_1 f ea er)
  
let mktac2 :
  'a 'b 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun er  ->
              mk name (Prims.parse_int "3") nunivs
                (mk_tactic_interpretation_2 f ea eb er)
  
let mktac3 :
  'a 'b 'c 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'c FStar_Syntax_Embeddings.embedding ->
                'r FStar_Syntax_Embeddings.embedding ->
                  FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun ec  ->
              fun er  ->
                mk name (Prims.parse_int "4") nunivs
                  (mk_tactic_interpretation_3 f ea eb ec er)
  
let mktac4 :
  'a 'b 'c 'd 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'c -> 'd -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'c FStar_Syntax_Embeddings.embedding ->
                'd FStar_Syntax_Embeddings.embedding ->
                  'r FStar_Syntax_Embeddings.embedding ->
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
                  mk name (Prims.parse_int "5") nunivs
                    (mk_tactic_interpretation_4 f ea eb ec ed er)
  
let mktac5 :
  'a 'b 'c 'd 'e 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'c FStar_Syntax_Embeddings.embedding ->
                'd FStar_Syntax_Embeddings.embedding ->
                  'e FStar_Syntax_Embeddings.embedding ->
                    'r FStar_Syntax_Embeddings.embedding ->
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
                    mk name (Prims.parse_int "6") nunivs
                      (mk_tactic_interpretation_5 f ea eb ec ed ee er)
  
let (mkt :
  Prims.string ->
    Prims.int ->
      Prims.int ->
        (FStar_TypeChecker_Cfg.psc ->
           FStar_Syntax_Syntax.args ->
             FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
          -> FStar_TypeChecker_Cfg.primitive_step)
  =
  fun nm  ->
    fun arity  ->
      fun nunivs  ->
        fun interpretation  ->
          let nm1 =
            FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]  in
          {
            FStar_TypeChecker_Cfg.name = nm1;
            FStar_TypeChecker_Cfg.arity = arity;
            FStar_TypeChecker_Cfg.univ_arity = nunivs;
            FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
            FStar_TypeChecker_Cfg.strong_reduction_ok = true;
            FStar_TypeChecker_Cfg.requires_binder_substitution = false;
            FStar_TypeChecker_Cfg.interpretation = interpretation;
            FStar_TypeChecker_Cfg.interpretation_nbe =
              (FStar_TypeChecker_NBETerm.dummy_interp nm1)
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
            let uu____3270 = extract_1 ea args  in
            FStar_Util.bind_opt uu____3270
              (fun a  ->
                 let r = f a  in
                 let uu____3278 =
                   let uu____3279 = FStar_TypeChecker_Cfg.psc_range psc  in
                   FStar_Syntax_Embeddings.embed er uu____3279 r  in
                 FStar_Pervasives_Native.Some uu____3278)
  
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
              let uu____3355 = extract_2 ea eb args  in
              FStar_Util.bind_opt uu____3355
                (fun uu____3371  ->
                   match uu____3371 with
                   | (a,b) ->
                       let r = f a b  in
                       let uu____3381 =
                         let uu____3382 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         FStar_Syntax_Embeddings.embed er uu____3382 r  in
                       FStar_Pervasives_Native.Some uu____3381)
  
let mktot1 :
  'a 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'r) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun er  ->
            mk name (Prims.parse_int "1") nunivs
              (mk_total_interpretation_1 f ea er)
  
let mktot2 :
  'a 'b 'r .
    Prims.int ->
      Prims.string ->
        ('a -> 'b -> 'r) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'b FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun er  ->
              mk name (Prims.parse_int "2") nunivs
                (mk_total_interpretation_2 f ea eb er)
  