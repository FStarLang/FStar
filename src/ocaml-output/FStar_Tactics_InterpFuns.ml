open Prims
let unembed :
  'uuuuuu8 .
    'uuuuuu8 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuuu8 FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n  ->
        let uu____32 = FStar_Syntax_Embeddings.unembed e t  in
        uu____32 true n
  
let embed :
  'uuuuuu51 .
    'uuuuuu51 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'uuuuuu51 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun rng  ->
      fun t  ->
        fun n  ->
          let uu____78 = FStar_Syntax_Embeddings.embed e t  in
          uu____78 rng FStar_Pervasives_Native.None n
  
let rec drop :
  'uuuuuu94 . Prims.int -> 'uuuuuu94 Prims.list -> 'uuuuuu94 Prims.list =
  fun n  ->
    fun l  ->
      if n = Prims.int_zero
      then l
      else
        (match l with
         | [] -> failwith "drop: impossible"
         | uu____123::xs -> drop (n - Prims.int_one) xs)
  
let timing_int :
  'uuuuuu147 'uuuuuu148 'uuuuuu149 'uuuuuu150 .
    FStar_Ident.lid ->
      ('uuuuuu147 -> 'uuuuuu148 -> 'uuuuuu149 -> 'uuuuuu150) ->
        'uuuuuu147 -> 'uuuuuu148 -> 'uuuuuu149 -> 'uuuuuu150
  =
  fun l  ->
    fun f  -> fun psc  -> fun cb  -> fun args  -> let r = f psc cb args  in r
  
let timing_nbe :
  'uuuuuu207 'uuuuuu208 'uuuuuu209 .
    FStar_Ident.lid ->
      ('uuuuuu207 -> 'uuuuuu208 -> 'uuuuuu209) ->
        'uuuuuu207 -> 'uuuuuu208 -> 'uuuuuu209
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
            let nm1 = FStar_Parser_Const.fstar_tactics_lid' ["Builtins"; nm]
               in
            {
              FStar_TypeChecker_Cfg.name = nm1;
              FStar_TypeChecker_Cfg.arity = arity;
              FStar_TypeChecker_Cfg.univ_arity = nunivs;
              FStar_TypeChecker_Cfg.auto_reflect =
                (FStar_Pervasives_Native.Some (arity - Prims.int_one));
              FStar_TypeChecker_Cfg.strong_reduction_ok = true;
              FStar_TypeChecker_Cfg.requires_binder_substitution = true;
              FStar_TypeChecker_Cfg.interpretation = (timing_int nm1 interp);
              FStar_TypeChecker_Cfg.interpretation_nbe =
                (timing_nbe nm1 nbe_interp)
            }
  
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
            let nm1 = FStar_Parser_Const.fstar_tactics_lid' ["Builtins"; nm]
               in
            {
              FStar_TypeChecker_Cfg.name = nm1;
              FStar_TypeChecker_Cfg.arity = arity;
              FStar_TypeChecker_Cfg.univ_arity = nunivs;
              FStar_TypeChecker_Cfg.auto_reflect =
                FStar_Pervasives_Native.None;
              FStar_TypeChecker_Cfg.strong_reduction_ok = true;
              FStar_TypeChecker_Cfg.requires_binder_substitution = true;
              FStar_TypeChecker_Cfg.interpretation = (timing_int nm1 interp);
              FStar_TypeChecker_Cfg.interpretation_nbe =
                (timing_nbe nm1 nbe_interp)
            }
  
let mk_total_interpretation_1_psc :
  'r 't1 .
    (FStar_TypeChecker_Cfg.psc -> 't1 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        'r FStar_Syntax_Embeddings.embedding ->
          FStar_TypeChecker_Cfg.psc ->
            FStar_Syntax_Embeddings.norm_cb ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun er  ->
        fun psc  ->
          fun ncb  ->
            fun args  ->
              match args with
              | (a1,uu____474)::[] ->
                  let uu____499 = unembed e1 a1 ncb  in
                  FStar_Util.bind_opt uu____499
                    (fun a11  ->
                       let r1 = f psc a11  in
                       let uu____507 =
                         let uu____508 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         embed er uu____508 r1 ncb  in
                       FStar_Pervasives_Native.Some uu____507)
              | uu____509 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_1_psc :
  'r 't1 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      (FStar_TypeChecker_Cfg.psc -> 't1 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun er  ->
          fun args  ->
            match args with
            | (a1,uu____573)::[] ->
                let uu____582 = FStar_TypeChecker_NBETerm.unembed e1 cb a1
                   in
                FStar_Util.bind_opt uu____582
                  (fun a11  ->
                     let r1 = f FStar_TypeChecker_Cfg.null_psc a11  in
                     let uu____590 = FStar_TypeChecker_NBETerm.embed er cb r1
                        in
                     FStar_Pervasives_Native.Some uu____590)
            | uu____591 -> FStar_Pervasives_Native.None
  
let mk_total_step_1_psc :
  'a 'na 'nr 'r .
    Prims.int ->
      Prims.string ->
        (FStar_TypeChecker_Cfg.psc -> 'a -> 'r) ->
          'a FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              (FStar_TypeChecker_Cfg.psc -> 'na -> 'nr) ->
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
                  mkt name Prims.int_one nunivs
                    (mk_total_interpretation_1_psc f ea er)
                    (fun cb  ->
                       fun args  ->
                         let uu____707 = drop nunivs args  in
                         mk_total_nbe_interpretation_1_psc cb nf nea ner
                           uu____707)
  
let mk_tactic_interpretation_1 :
  'r 't1 .
    ('t1 -> 'r FStar_Tactics_Monad.tac) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        'r FStar_Syntax_Embeddings.embedding ->
          FStar_TypeChecker_Cfg.psc ->
            FStar_Syntax_Embeddings.norm_cb ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun er  ->
        fun psc  ->
          fun ncb  ->
            fun args  ->
              match args with
              | (a1,uu____783)::(a2,uu____785)::[] ->
                  let uu____826 = unembed e1 a1 ncb  in
                  FStar_Util.bind_opt uu____826
                    (fun a11  ->
                       let uu____832 =
                         unembed FStar_Tactics_Embedding.e_proofstate a2 ncb
                          in
                       FStar_Util.bind_opt uu____832
                         (fun ps  ->
                            let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                               in
                            let r1 =
                              let uu____844 = t a11  in
                              FStar_Tactics_Monad.run_safe uu____844 ps1  in
                            let uu____847 =
                              let uu____848 =
                                FStar_Tactics_Embedding.e_result er  in
                              let uu____853 =
                                FStar_TypeChecker_Cfg.psc_range psc  in
                              embed uu____848 uu____853 r1 ncb  in
                            FStar_Pervasives_Native.Some uu____847))
              | uu____856 -> FStar_Pervasives_Native.None
  
let mk_tactic_interpretation_2 :
  'r 't1 't2 .
    ('t1 -> 't2 -> 'r FStar_Tactics_Monad.tac) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_TypeChecker_Cfg.psc ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun e2  ->
        fun er  ->
          fun psc  ->
            fun ncb  ->
              fun args  ->
                match args with
                | (a1,uu____947)::(a2,uu____949)::(a3,uu____951)::[] ->
                    let uu____1008 = unembed e1 a1 ncb  in
                    FStar_Util.bind_opt uu____1008
                      (fun a11  ->
                         let uu____1014 = unembed e2 a2 ncb  in
                         FStar_Util.bind_opt uu____1014
                           (fun a21  ->
                              let uu____1020 =
                                unembed FStar_Tactics_Embedding.e_proofstate
                                  a3 ncb
                                 in
                              FStar_Util.bind_opt uu____1020
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   let r1 =
                                     let uu____1032 = t a11 a21  in
                                     FStar_Tactics_Monad.run_safe uu____1032
                                       ps1
                                      in
                                   let uu____1035 =
                                     let uu____1036 =
                                       FStar_Tactics_Embedding.e_result er
                                        in
                                     let uu____1041 =
                                       FStar_TypeChecker_Cfg.psc_range psc
                                        in
                                     embed uu____1036 uu____1041 r1 ncb  in
                                   FStar_Pervasives_Native.Some uu____1035)))
                | uu____1044 -> FStar_Pervasives_Native.None
  
let mk_tactic_interpretation_3 :
  'r 't1 't2 't3 .
    ('t1 -> 't2 -> 't3 -> 'r FStar_Tactics_Monad.tac) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_TypeChecker_Cfg.psc ->
                FStar_Syntax_Embeddings.norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun er  ->
            fun psc  ->
              fun ncb  ->
                fun args  ->
                  match args with
                  | (a1,uu____1154)::(a2,uu____1156)::(a3,uu____1158)::
                      (a4,uu____1160)::[] ->
                      let uu____1233 = unembed e1 a1 ncb  in
                      FStar_Util.bind_opt uu____1233
                        (fun a11  ->
                           let uu____1239 = unembed e2 a2 ncb  in
                           FStar_Util.bind_opt uu____1239
                             (fun a21  ->
                                let uu____1245 = unembed e3 a3 ncb  in
                                FStar_Util.bind_opt uu____1245
                                  (fun a31  ->
                                     let uu____1251 =
                                       unembed
                                         FStar_Tactics_Embedding.e_proofstate
                                         a4 ncb
                                        in
                                     FStar_Util.bind_opt uu____1251
                                       (fun ps  ->
                                          let ps1 =
                                            FStar_Tactics_Types.set_ps_psc
                                              psc ps
                                             in
                                          let r1 =
                                            let uu____1263 = t a11 a21 a31
                                               in
                                            FStar_Tactics_Monad.run_safe
                                              uu____1263 ps1
                                             in
                                          let uu____1266 =
                                            let uu____1267 =
                                              FStar_Tactics_Embedding.e_result
                                                er
                                               in
                                            let uu____1272 =
                                              FStar_TypeChecker_Cfg.psc_range
                                                psc
                                               in
                                            embed uu____1267 uu____1272 r1
                                              ncb
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1266))))
                  | uu____1275 -> FStar_Pervasives_Native.None
  
let mk_tactic_interpretation_4 :
  'r 't1 't2 't3 't4 .
    ('t1 -> 't2 -> 't3 -> 't4 -> 'r FStar_Tactics_Monad.tac) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                FStar_TypeChecker_Cfg.psc ->
                  FStar_Syntax_Embeddings.norm_cb ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun er  ->
              fun psc  ->
                fun ncb  ->
                  fun args  ->
                    match args with
                    | (a1,uu____1404)::(a2,uu____1406)::(a3,uu____1408)::
                        (a4,uu____1410)::(a5,uu____1412)::[] ->
                        let uu____1501 = unembed e1 a1 ncb  in
                        FStar_Util.bind_opt uu____1501
                          (fun a11  ->
                             let uu____1507 = unembed e2 a2 ncb  in
                             FStar_Util.bind_opt uu____1507
                               (fun a21  ->
                                  let uu____1513 = unembed e3 a3 ncb  in
                                  FStar_Util.bind_opt uu____1513
                                    (fun a31  ->
                                       let uu____1519 = unembed e4 a4 ncb  in
                                       FStar_Util.bind_opt uu____1519
                                         (fun a41  ->
                                            let uu____1525 =
                                              unembed
                                                FStar_Tactics_Embedding.e_proofstate
                                                a5 ncb
                                               in
                                            FStar_Util.bind_opt uu____1525
                                              (fun ps  ->
                                                 let ps1 =
                                                   FStar_Tactics_Types.set_ps_psc
                                                     psc ps
                                                    in
                                                 let r1 =
                                                   let uu____1537 =
                                                     t a11 a21 a31 a41  in
                                                   FStar_Tactics_Monad.run_safe
                                                     uu____1537 ps1
                                                    in
                                                 let uu____1540 =
                                                   let uu____1541 =
                                                     FStar_Tactics_Embedding.e_result
                                                       er
                                                      in
                                                   let uu____1546 =
                                                     FStar_TypeChecker_Cfg.psc_range
                                                       psc
                                                      in
                                                   embed uu____1541
                                                     uu____1546 r1 ncb
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____1540)))))
                    | uu____1549 -> FStar_Pervasives_Native.None
  
let mk_tactic_interpretation_5 :
  'r 't1 't2 't3 't4 't5 .
    ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r FStar_Tactics_Monad.tac) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              't5 FStar_Syntax_Embeddings.embedding ->
                'r FStar_Syntax_Embeddings.embedding ->
                  FStar_TypeChecker_Cfg.psc ->
                    FStar_Syntax_Embeddings.norm_cb ->
                      FStar_Syntax_Syntax.args ->
                        FStar_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun er  ->
                fun psc  ->
                  fun ncb  ->
                    fun args  ->
                      match args with
                      | (a1,uu____1697)::(a2,uu____1699)::(a3,uu____1701)::
                          (a4,uu____1703)::(a5,uu____1705)::(a6,uu____1707)::[]
                          ->
                          let uu____1812 = unembed e1 a1 ncb  in
                          FStar_Util.bind_opt uu____1812
                            (fun a11  ->
                               let uu____1818 = unembed e2 a2 ncb  in
                               FStar_Util.bind_opt uu____1818
                                 (fun a21  ->
                                    let uu____1824 = unembed e3 a3 ncb  in
                                    FStar_Util.bind_opt uu____1824
                                      (fun a31  ->
                                         let uu____1830 = unembed e4 a4 ncb
                                            in
                                         FStar_Util.bind_opt uu____1830
                                           (fun a41  ->
                                              let uu____1836 =
                                                unembed e5 a5 ncb  in
                                              FStar_Util.bind_opt uu____1836
                                                (fun a51  ->
                                                   let uu____1842 =
                                                     unembed
                                                       FStar_Tactics_Embedding.e_proofstate
                                                       a6 ncb
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____1842
                                                     (fun ps  ->
                                                        let ps1 =
                                                          FStar_Tactics_Types.set_ps_psc
                                                            psc ps
                                                           in
                                                        let r1 =
                                                          let uu____1854 =
                                                            t a11 a21 a31 a41
                                                              a51
                                                             in
                                                          FStar_Tactics_Monad.run_safe
                                                            uu____1854 ps1
                                                           in
                                                        let uu____1857 =
                                                          let uu____1858 =
                                                            FStar_Tactics_Embedding.e_result
                                                              er
                                                             in
                                                          let uu____1863 =
                                                            FStar_TypeChecker_Cfg.psc_range
                                                              psc
                                                             in
                                                          embed uu____1858
                                                            uu____1863 r1 ncb
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____1857))))))
                      | uu____1866 -> FStar_Pervasives_Native.None
  
let mk_tactic_interpretation_6 :
  'r 't1 't2 't3 't4 't5 't6 .
    ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r FStar_Tactics_Monad.tac) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              't5 FStar_Syntax_Embeddings.embedding ->
                't6 FStar_Syntax_Embeddings.embedding ->
                  'r FStar_Syntax_Embeddings.embedding ->
                    FStar_TypeChecker_Cfg.psc ->
                      FStar_Syntax_Embeddings.norm_cb ->
                        FStar_Syntax_Syntax.args ->
                          FStar_Syntax_Syntax.term
                            FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun er  ->
                  fun psc  ->
                    fun ncb  ->
                      fun args  ->
                        match args with
                        | (a1,uu____2033)::(a2,uu____2035)::(a3,uu____2037)::
                            (a4,uu____2039)::(a5,uu____2041)::(a6,uu____2043)::
                            (a7,uu____2045)::[] ->
                            let uu____2166 = unembed e1 a1 ncb  in
                            FStar_Util.bind_opt uu____2166
                              (fun a11  ->
                                 let uu____2172 = unembed e2 a2 ncb  in
                                 FStar_Util.bind_opt uu____2172
                                   (fun a21  ->
                                      let uu____2178 = unembed e3 a3 ncb  in
                                      FStar_Util.bind_opt uu____2178
                                        (fun a31  ->
                                           let uu____2184 = unembed e4 a4 ncb
                                              in
                                           FStar_Util.bind_opt uu____2184
                                             (fun a41  ->
                                                let uu____2190 =
                                                  unembed e5 a5 ncb  in
                                                FStar_Util.bind_opt
                                                  uu____2190
                                                  (fun a51  ->
                                                     let uu____2196 =
                                                       unembed e6 a6 ncb  in
                                                     FStar_Util.bind_opt
                                                       uu____2196
                                                       (fun a61  ->
                                                          let uu____2202 =
                                                            unembed
                                                              FStar_Tactics_Embedding.e_proofstate
                                                              a7 ncb
                                                             in
                                                          FStar_Util.bind_opt
                                                            uu____2202
                                                            (fun ps  ->
                                                               let ps1 =
                                                                 FStar_Tactics_Types.set_ps_psc
                                                                   psc ps
                                                                  in
                                                               let r1 =
                                                                 let uu____2214
                                                                   =
                                                                   t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    in
                                                                 FStar_Tactics_Monad.run_safe
                                                                   uu____2214
                                                                   ps1
                                                                  in
                                                               let uu____2217
                                                                 =
                                                                 let uu____2218
                                                                   =
                                                                   FStar_Tactics_Embedding.e_result
                                                                    er
                                                                    in
                                                                 let uu____2223
                                                                   =
                                                                   FStar_TypeChecker_Cfg.psc_range
                                                                    psc
                                                                    in
                                                                 embed
                                                                   uu____2218
                                                                   uu____2223
                                                                   r1 ncb
                                                                  in
                                                               FStar_Pervasives_Native.Some
                                                                 uu____2217)))))))
                        | uu____2226 -> FStar_Pervasives_Native.None
  
let mk_tactic_interpretation_7 :
  'r 't1 't2 't3 't4 't5 't6 't7 .
    ('t1 ->
       't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r FStar_Tactics_Monad.tac)
      ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              't5 FStar_Syntax_Embeddings.embedding ->
                't6 FStar_Syntax_Embeddings.embedding ->
                  't7 FStar_Syntax_Embeddings.embedding ->
                    'r FStar_Syntax_Embeddings.embedding ->
                      FStar_TypeChecker_Cfg.psc ->
                        FStar_Syntax_Embeddings.norm_cb ->
                          FStar_Syntax_Syntax.args ->
                            FStar_Syntax_Syntax.term
                              FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun e7  ->
                  fun er  ->
                    fun psc  ->
                      fun ncb  ->
                        fun args  ->
                          match args with
                          | (a1,uu____2412)::(a2,uu____2414)::(a3,uu____2416)::
                              (a4,uu____2418)::(a5,uu____2420)::(a6,uu____2422)::
                              (a7,uu____2424)::(a8,uu____2426)::[] ->
                              let uu____2563 = unembed e1 a1 ncb  in
                              FStar_Util.bind_opt uu____2563
                                (fun a11  ->
                                   let uu____2569 = unembed e2 a2 ncb  in
                                   FStar_Util.bind_opt uu____2569
                                     (fun a21  ->
                                        let uu____2575 = unembed e3 a3 ncb
                                           in
                                        FStar_Util.bind_opt uu____2575
                                          (fun a31  ->
                                             let uu____2581 =
                                               unembed e4 a4 ncb  in
                                             FStar_Util.bind_opt uu____2581
                                               (fun a41  ->
                                                  let uu____2587 =
                                                    unembed e5 a5 ncb  in
                                                  FStar_Util.bind_opt
                                                    uu____2587
                                                    (fun a51  ->
                                                       let uu____2593 =
                                                         unembed e6 a6 ncb
                                                          in
                                                       FStar_Util.bind_opt
                                                         uu____2593
                                                         (fun a61  ->
                                                            let uu____2599 =
                                                              unembed e7 a7
                                                                ncb
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____2599
                                                              (fun a71  ->
                                                                 let uu____2605
                                                                   =
                                                                   unembed
                                                                    FStar_Tactics_Embedding.e_proofstate
                                                                    a8 ncb
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____2605
                                                                   (fun ps 
                                                                    ->
                                                                    let ps1 =
                                                                    FStar_Tactics_Types.set_ps_psc
                                                                    psc ps
                                                                     in
                                                                    let r1 =
                                                                    let uu____2617
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71  in
                                                                    FStar_Tactics_Monad.run_safe
                                                                    uu____2617
                                                                    ps1  in
                                                                    let uu____2620
                                                                    =
                                                                    let uu____2621
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                    let uu____2626
                                                                    =
                                                                    FStar_TypeChecker_Cfg.psc_range
                                                                    psc  in
                                                                    embed
                                                                    uu____2621
                                                                    uu____2626
                                                                    r1 ncb
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____2620))))))))
                          | uu____2629 -> FStar_Pervasives_Native.None
  
let mk_tactic_interpretation_8 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 .
    ('t1 ->
       't2 ->
         't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r FStar_Tactics_Monad.tac)
      ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              't5 FStar_Syntax_Embeddings.embedding ->
                't6 FStar_Syntax_Embeddings.embedding ->
                  't7 FStar_Syntax_Embeddings.embedding ->
                    't8 FStar_Syntax_Embeddings.embedding ->
                      'r FStar_Syntax_Embeddings.embedding ->
                        FStar_TypeChecker_Cfg.psc ->
                          FStar_Syntax_Embeddings.norm_cb ->
                            FStar_Syntax_Syntax.args ->
                              FStar_Syntax_Syntax.term
                                FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun e7  ->
                  fun e8  ->
                    fun er  ->
                      fun psc  ->
                        fun ncb  ->
                          fun args  ->
                            match args with
                            | (a1,uu____2834)::(a2,uu____2836)::(a3,uu____2838)::
                                (a4,uu____2840)::(a5,uu____2842)::(a6,uu____2844)::
                                (a7,uu____2846)::(a8,uu____2848)::(a9,uu____2850)::[]
                                ->
                                let uu____3003 = unembed e1 a1 ncb  in
                                FStar_Util.bind_opt uu____3003
                                  (fun a11  ->
                                     let uu____3009 = unembed e2 a2 ncb  in
                                     FStar_Util.bind_opt uu____3009
                                       (fun a21  ->
                                          let uu____3015 = unembed e3 a3 ncb
                                             in
                                          FStar_Util.bind_opt uu____3015
                                            (fun a31  ->
                                               let uu____3021 =
                                                 unembed e4 a4 ncb  in
                                               FStar_Util.bind_opt uu____3021
                                                 (fun a41  ->
                                                    let uu____3027 =
                                                      unembed e5 a5 ncb  in
                                                    FStar_Util.bind_opt
                                                      uu____3027
                                                      (fun a51  ->
                                                         let uu____3033 =
                                                           unembed e6 a6 ncb
                                                            in
                                                         FStar_Util.bind_opt
                                                           uu____3033
                                                           (fun a61  ->
                                                              let uu____3039
                                                                =
                                                                unembed e7 a7
                                                                  ncb
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____3039
                                                                (fun a71  ->
                                                                   let uu____3045
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb
                                                                     in
                                                                   FStar_Util.bind_opt
                                                                    uu____3045
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____3051
                                                                    =
                                                                    unembed
                                                                    FStar_Tactics_Embedding.e_proofstate
                                                                    a9 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____3051
                                                                    (fun ps 
                                                                    ->
                                                                    let ps1 =
                                                                    FStar_Tactics_Types.set_ps_psc
                                                                    psc ps
                                                                     in
                                                                    let r1 =
                                                                    let uu____3063
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                     in
                                                                    FStar_Tactics_Monad.run_safe
                                                                    uu____3063
                                                                    ps1  in
                                                                    let uu____3066
                                                                    =
                                                                    let uu____3067
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                    let uu____3072
                                                                    =
                                                                    FStar_TypeChecker_Cfg.psc_range
                                                                    psc  in
                                                                    embed
                                                                    uu____3067
                                                                    uu____3072
                                                                    r1 ncb
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3066)))))))))
                            | uu____3075 -> FStar_Pervasives_Native.None
  
let mk_tactic_interpretation_9 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 't9 .
    ('t1 ->
       't2 ->
         't3 ->
           't4 ->
             't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r FStar_Tactics_Monad.tac)
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
                        'r FStar_Syntax_Embeddings.embedding ->
                          FStar_TypeChecker_Cfg.psc ->
                            FStar_Syntax_Embeddings.norm_cb ->
                              FStar_Syntax_Syntax.args ->
                                FStar_Syntax_Syntax.term
                                  FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun e7  ->
                  fun e8  ->
                    fun e9  ->
                      fun er  ->
                        fun psc  ->
                          fun ncb  ->
                            fun args  ->
                              match args with
                              | (a1,uu____3299)::(a2,uu____3301)::(a3,uu____3303)::
                                  (a4,uu____3305)::(a5,uu____3307)::(a6,uu____3309)::
                                  (a7,uu____3311)::(a8,uu____3313)::(a9,uu____3315)::
                                  (a10,uu____3317)::[] ->
                                  let uu____3486 = unembed e1 a1 ncb  in
                                  FStar_Util.bind_opt uu____3486
                                    (fun a11  ->
                                       let uu____3492 = unembed e2 a2 ncb  in
                                       FStar_Util.bind_opt uu____3492
                                         (fun a21  ->
                                            let uu____3498 =
                                              unembed e3 a3 ncb  in
                                            FStar_Util.bind_opt uu____3498
                                              (fun a31  ->
                                                 let uu____3504 =
                                                   unembed e4 a4 ncb  in
                                                 FStar_Util.bind_opt
                                                   uu____3504
                                                   (fun a41  ->
                                                      let uu____3510 =
                                                        unembed e5 a5 ncb  in
                                                      FStar_Util.bind_opt
                                                        uu____3510
                                                        (fun a51  ->
                                                           let uu____3516 =
                                                             unembed e6 a6
                                                               ncb
                                                              in
                                                           FStar_Util.bind_opt
                                                             uu____3516
                                                             (fun a61  ->
                                                                let uu____3522
                                                                  =
                                                                  unembed e7
                                                                    a7 ncb
                                                                   in
                                                                FStar_Util.bind_opt
                                                                  uu____3522
                                                                  (fun a71 
                                                                    ->
                                                                    let uu____3528
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____3528
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____3534
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____3534
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____3540
                                                                    =
                                                                    unembed
                                                                    FStar_Tactics_Embedding.e_proofstate
                                                                    a10 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____3540
                                                                    (fun ps 
                                                                    ->
                                                                    let ps1 =
                                                                    FStar_Tactics_Types.set_ps_psc
                                                                    psc ps
                                                                     in
                                                                    let r1 =
                                                                    let uu____3552
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91  in
                                                                    FStar_Tactics_Monad.run_safe
                                                                    uu____3552
                                                                    ps1  in
                                                                    let uu____3555
                                                                    =
                                                                    let uu____3556
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                    let uu____3561
                                                                    =
                                                                    FStar_TypeChecker_Cfg.psc_range
                                                                    psc  in
                                                                    embed
                                                                    uu____3556
                                                                    uu____3561
                                                                    r1 ncb
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3555))))))))))
                              | uu____3564 -> FStar_Pervasives_Native.None
  
let mk_tactic_interpretation_10 :
  'r 't1 't10 't2 't3 't4 't5 't6 't7 't8 't9 .
    ('t1 ->
       't2 ->
         't3 ->
           't4 ->
             't5 ->
               't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r FStar_Tactics_Monad.tac)
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
                          'r FStar_Syntax_Embeddings.embedding ->
                            FStar_TypeChecker_Cfg.psc ->
                              FStar_Syntax_Embeddings.norm_cb ->
                                FStar_Syntax_Syntax.args ->
                                  FStar_Syntax_Syntax.term
                                    FStar_Pervasives_Native.option
  =
  fun t  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun e7  ->
                  fun e8  ->
                    fun e9  ->
                      fun e10  ->
                        fun er  ->
                          fun psc  ->
                            fun ncb  ->
                              fun args  ->
                                match args with
                                | (a1,uu____3807)::(a2,uu____3809)::(a3,uu____3811)::
                                    (a4,uu____3813)::(a5,uu____3815)::
                                    (a6,uu____3817)::(a7,uu____3819)::
                                    (a8,uu____3821)::(a9,uu____3823)::
                                    (a10,uu____3825)::(a11,uu____3827)::[] ->
                                    let uu____4012 = unembed e1 a1 ncb  in
                                    FStar_Util.bind_opt uu____4012
                                      (fun a12  ->
                                         let uu____4018 = unembed e2 a2 ncb
                                            in
                                         FStar_Util.bind_opt uu____4018
                                           (fun a21  ->
                                              let uu____4024 =
                                                unembed e3 a3 ncb  in
                                              FStar_Util.bind_opt uu____4024
                                                (fun a31  ->
                                                   let uu____4030 =
                                                     unembed e4 a4 ncb  in
                                                   FStar_Util.bind_opt
                                                     uu____4030
                                                     (fun a41  ->
                                                        let uu____4036 =
                                                          unembed e5 a5 ncb
                                                           in
                                                        FStar_Util.bind_opt
                                                          uu____4036
                                                          (fun a51  ->
                                                             let uu____4042 =
                                                               unembed e6 a6
                                                                 ncb
                                                                in
                                                             FStar_Util.bind_opt
                                                               uu____4042
                                                               (fun a61  ->
                                                                  let uu____4048
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb
                                                                     in
                                                                  FStar_Util.bind_opt
                                                                    uu____4048
                                                                    (
                                                                    fun a71 
                                                                    ->
                                                                    let uu____4054
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____4054
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____4060
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____4060
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____4066
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____4066
                                                                    (fun a101
                                                                     ->
                                                                    let uu____4072
                                                                    =
                                                                    unembed
                                                                    FStar_Tactics_Embedding.e_proofstate
                                                                    a11 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____4072
                                                                    (fun ps 
                                                                    ->
                                                                    let ps1 =
                                                                    FStar_Tactics_Types.set_ps_psc
                                                                    psc ps
                                                                     in
                                                                    let r1 =
                                                                    let uu____4084
                                                                    =
                                                                    t a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                     in
                                                                    FStar_Tactics_Monad.run_safe
                                                                    uu____4084
                                                                    ps1  in
                                                                    let uu____4087
                                                                    =
                                                                    let uu____4088
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result
                                                                    er  in
                                                                    let uu____4093
                                                                    =
                                                                    FStar_TypeChecker_Cfg.psc_range
                                                                    psc  in
                                                                    embed
                                                                    uu____4088
                                                                    uu____4093
                                                                    r1 ncb
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4087)))))))))))
                                | uu____4096 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_1 :
  'r 't1 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 'r FStar_Tactics_Monad.tac) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun er  ->
          fun args  ->
            match args with
            | (a1,uu____4159)::(a2,uu____4161)::[] ->
                let uu____4174 = FStar_TypeChecker_NBETerm.unembed e1 cb a1
                   in
                FStar_Util.bind_opt uu____4174
                  (fun a11  ->
                     let uu____4180 =
                       FStar_TypeChecker_NBETerm.unembed
                         FStar_Tactics_Embedding.e_proofstate_nbe cb a2
                        in
                     FStar_Util.bind_opt uu____4180
                       (fun ps  ->
                          let r1 =
                            let uu____4190 = t a11  in
                            FStar_Tactics_Monad.run_safe uu____4190 ps  in
                          let uu____4193 =
                            let uu____4194 =
                              FStar_Tactics_Embedding.e_result_nbe er  in
                            FStar_TypeChecker_NBETerm.embed uu____4194 cb r1
                             in
                          FStar_Pervasives_Native.Some uu____4193))
            | uu____4201 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_2 :
  'r 't1 't2 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 'r FStar_Tactics_Monad.tac) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            'r FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.args ->
                FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          fun er  ->
            fun args  ->
              match args with
              | (a1,uu____4283)::(a2,uu____4285)::(a3,uu____4287)::[] ->
                  let uu____4304 = FStar_TypeChecker_NBETerm.unembed e1 cb a1
                     in
                  FStar_Util.bind_opt uu____4304
                    (fun a11  ->
                       let uu____4310 =
                         FStar_TypeChecker_NBETerm.unembed e2 cb a2  in
                       FStar_Util.bind_opt uu____4310
                         (fun a21  ->
                            let uu____4316 =
                              FStar_TypeChecker_NBETerm.unembed
                                FStar_Tactics_Embedding.e_proofstate_nbe cb
                                a3
                               in
                            FStar_Util.bind_opt uu____4316
                              (fun ps  ->
                                 let r1 =
                                   let uu____4326 = t a11 a21  in
                                   FStar_Tactics_Monad.run_safe uu____4326 ps
                                    in
                                 let uu____4329 =
                                   let uu____4330 =
                                     FStar_Tactics_Embedding.e_result_nbe er
                                      in
                                   FStar_TypeChecker_NBETerm.embed uu____4330
                                     cb r1
                                    in
                                 FStar_Pervasives_Native.Some uu____4329)))
              | uu____4337 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_3 :
  'r 't1 't2 't3 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 'r FStar_Tactics_Monad.tac) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              'r FStar_TypeChecker_NBETerm.embedding ->
                FStar_TypeChecker_NBETerm.args ->
                  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun er  ->
              fun args  ->
                match args with
                | (a1,uu____4438)::(a2,uu____4440)::(a3,uu____4442)::
                    (a4,uu____4444)::[] ->
                    let uu____4465 =
                      FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                    FStar_Util.bind_opt uu____4465
                      (fun a11  ->
                         let uu____4471 =
                           FStar_TypeChecker_NBETerm.unembed e2 cb a2  in
                         FStar_Util.bind_opt uu____4471
                           (fun a21  ->
                              let uu____4477 =
                                FStar_TypeChecker_NBETerm.unembed e3 cb a3
                                 in
                              FStar_Util.bind_opt uu____4477
                                (fun a31  ->
                                   let uu____4483 =
                                     FStar_TypeChecker_NBETerm.unembed
                                       FStar_Tactics_Embedding.e_proofstate_nbe
                                       cb a4
                                      in
                                   FStar_Util.bind_opt uu____4483
                                     (fun ps  ->
                                        let r1 =
                                          let uu____4493 = t a11 a21 a31  in
                                          FStar_Tactics_Monad.run_safe
                                            uu____4493 ps
                                           in
                                        let uu____4496 =
                                          let uu____4497 =
                                            FStar_Tactics_Embedding.e_result_nbe
                                              er
                                             in
                                          FStar_TypeChecker_NBETerm.embed
                                            uu____4497 cb r1
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____4496))))
                | uu____4504 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_4 :
  'r 't1 't2 't3 't4 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 'r FStar_Tactics_Monad.tac) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                'r FStar_TypeChecker_NBETerm.embedding ->
                  FStar_TypeChecker_NBETerm.args ->
                    FStar_TypeChecker_NBETerm.t
                      FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun er  ->
                fun args  ->
                  match args with
                  | (a1,uu____4624)::(a2,uu____4626)::(a3,uu____4628)::
                      (a4,uu____4630)::(a5,uu____4632)::[] ->
                      let uu____4657 =
                        FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                      FStar_Util.bind_opt uu____4657
                        (fun a11  ->
                           let uu____4663 =
                             FStar_TypeChecker_NBETerm.unembed e2 cb a2  in
                           FStar_Util.bind_opt uu____4663
                             (fun a21  ->
                                let uu____4669 =
                                  FStar_TypeChecker_NBETerm.unembed e3 cb a3
                                   in
                                FStar_Util.bind_opt uu____4669
                                  (fun a31  ->
                                     let uu____4675 =
                                       FStar_TypeChecker_NBETerm.unembed e4
                                         cb a4
                                        in
                                     FStar_Util.bind_opt uu____4675
                                       (fun a41  ->
                                          let uu____4681 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              FStar_Tactics_Embedding.e_proofstate_nbe
                                              cb a5
                                             in
                                          FStar_Util.bind_opt uu____4681
                                            (fun ps  ->
                                               let r1 =
                                                 let uu____4691 =
                                                   t a11 a21 a31 a41  in
                                                 FStar_Tactics_Monad.run_safe
                                                   uu____4691 ps
                                                  in
                                               let uu____4694 =
                                                 let uu____4695 =
                                                   FStar_Tactics_Embedding.e_result_nbe
                                                     er
                                                    in
                                                 FStar_TypeChecker_NBETerm.embed
                                                   uu____4695 cb r1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4694)))))
                  | uu____4702 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_5 :
  'r 't1 't2 't3 't4 't5 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r FStar_Tactics_Monad.tac) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  'r FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_NBETerm.args ->
                      FStar_TypeChecker_NBETerm.t
                        FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun er  ->
                  fun args  ->
                    match args with
                    | (a1,uu____4841)::(a2,uu____4843)::(a3,uu____4845)::
                        (a4,uu____4847)::(a5,uu____4849)::(a6,uu____4851)::[]
                        ->
                        let uu____4880 =
                          FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                        FStar_Util.bind_opt uu____4880
                          (fun a11  ->
                             let uu____4886 =
                               FStar_TypeChecker_NBETerm.unembed e2 cb a2  in
                             FStar_Util.bind_opt uu____4886
                               (fun a21  ->
                                  let uu____4892 =
                                    FStar_TypeChecker_NBETerm.unembed e3 cb
                                      a3
                                     in
                                  FStar_Util.bind_opt uu____4892
                                    (fun a31  ->
                                       let uu____4898 =
                                         FStar_TypeChecker_NBETerm.unembed e4
                                           cb a4
                                          in
                                       FStar_Util.bind_opt uu____4898
                                         (fun a41  ->
                                            let uu____4904 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                e5 cb a5
                                               in
                                            FStar_Util.bind_opt uu____4904
                                              (fun a51  ->
                                                 let uu____4910 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     FStar_Tactics_Embedding.e_proofstate_nbe
                                                     cb a6
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____4910
                                                   (fun ps  ->
                                                      let r1 =
                                                        let uu____4920 =
                                                          t a11 a21 a31 a41
                                                            a51
                                                           in
                                                        FStar_Tactics_Monad.run_safe
                                                          uu____4920 ps
                                                         in
                                                      let uu____4923 =
                                                        let uu____4924 =
                                                          FStar_Tactics_Embedding.e_result_nbe
                                                            er
                                                           in
                                                        FStar_TypeChecker_NBETerm.embed
                                                          uu____4924 cb r1
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____4923))))))
                    | uu____4931 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_6 :
  'r 't1 't2 't3 't4 't5 't6 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r FStar_Tactics_Monad.tac)
        ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    'r FStar_TypeChecker_NBETerm.embedding ->
                      FStar_TypeChecker_NBETerm.args ->
                        FStar_TypeChecker_NBETerm.t
                          FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun er  ->
                    fun args  ->
                      match args with
                      | (a1,uu____5089)::(a2,uu____5091)::(a3,uu____5093)::
                          (a4,uu____5095)::(a5,uu____5097)::(a6,uu____5099)::
                          (a7,uu____5101)::[] ->
                          let uu____5134 =
                            FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                          FStar_Util.bind_opt uu____5134
                            (fun a11  ->
                               let uu____5140 =
                                 FStar_TypeChecker_NBETerm.unembed e2 cb a2
                                  in
                               FStar_Util.bind_opt uu____5140
                                 (fun a21  ->
                                    let uu____5146 =
                                      FStar_TypeChecker_NBETerm.unembed e3 cb
                                        a3
                                       in
                                    FStar_Util.bind_opt uu____5146
                                      (fun a31  ->
                                         let uu____5152 =
                                           FStar_TypeChecker_NBETerm.unembed
                                             e4 cb a4
                                            in
                                         FStar_Util.bind_opt uu____5152
                                           (fun a41  ->
                                              let uu____5158 =
                                                FStar_TypeChecker_NBETerm.unembed
                                                  e5 cb a5
                                                 in
                                              FStar_Util.bind_opt uu____5158
                                                (fun a51  ->
                                                   let uu____5164 =
                                                     FStar_TypeChecker_NBETerm.unembed
                                                       e6 cb a6
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____5164
                                                     (fun a61  ->
                                                        let uu____5170 =
                                                          FStar_TypeChecker_NBETerm.unembed
                                                            FStar_Tactics_Embedding.e_proofstate_nbe
                                                            cb a7
                                                           in
                                                        FStar_Util.bind_opt
                                                          uu____5170
                                                          (fun ps  ->
                                                             let r1 =
                                                               let uu____5180
                                                                 =
                                                                 t a11 a21
                                                                   a31 a41
                                                                   a51 a61
                                                                  in
                                                               FStar_Tactics_Monad.run_safe
                                                                 uu____5180
                                                                 ps
                                                                in
                                                             let uu____5183 =
                                                               let uu____5184
                                                                 =
                                                                 FStar_Tactics_Embedding.e_result_nbe
                                                                   er
                                                                  in
                                                               FStar_TypeChecker_NBETerm.embed
                                                                 uu____5184
                                                                 cb r1
                                                                in
                                                             FStar_Pervasives_Native.Some
                                                               uu____5183)))))))
                      | uu____5191 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_7 :
  'r 't1 't2 't3 't4 't5 't6 't7 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 ->
         't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r FStar_Tactics_Monad.tac)
        ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    't7 FStar_TypeChecker_NBETerm.embedding ->
                      'r FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_NBETerm.args ->
                          FStar_TypeChecker_NBETerm.t
                            FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun e7  ->
                    fun er  ->
                      fun args  ->
                        match args with
                        | (a1,uu____5368)::(a2,uu____5370)::(a3,uu____5372)::
                            (a4,uu____5374)::(a5,uu____5376)::(a6,uu____5378)::
                            (a7,uu____5380)::(a8,uu____5382)::[] ->
                            let uu____5419 =
                              FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                            FStar_Util.bind_opt uu____5419
                              (fun a11  ->
                                 let uu____5425 =
                                   FStar_TypeChecker_NBETerm.unembed e2 cb a2
                                    in
                                 FStar_Util.bind_opt uu____5425
                                   (fun a21  ->
                                      let uu____5431 =
                                        FStar_TypeChecker_NBETerm.unembed e3
                                          cb a3
                                         in
                                      FStar_Util.bind_opt uu____5431
                                        (fun a31  ->
                                           let uu____5437 =
                                             FStar_TypeChecker_NBETerm.unembed
                                               e4 cb a4
                                              in
                                           FStar_Util.bind_opt uu____5437
                                             (fun a41  ->
                                                let uu____5443 =
                                                  FStar_TypeChecker_NBETerm.unembed
                                                    e5 cb a5
                                                   in
                                                FStar_Util.bind_opt
                                                  uu____5443
                                                  (fun a51  ->
                                                     let uu____5449 =
                                                       FStar_TypeChecker_NBETerm.unembed
                                                         e6 cb a6
                                                        in
                                                     FStar_Util.bind_opt
                                                       uu____5449
                                                       (fun a61  ->
                                                          let uu____5455 =
                                                            FStar_TypeChecker_NBETerm.unembed
                                                              e7 cb a7
                                                             in
                                                          FStar_Util.bind_opt
                                                            uu____5455
                                                            (fun a71  ->
                                                               let uu____5461
                                                                 =
                                                                 FStar_TypeChecker_NBETerm.unembed
                                                                   FStar_Tactics_Embedding.e_proofstate_nbe
                                                                   cb a8
                                                                  in
                                                               FStar_Util.bind_opt
                                                                 uu____5461
                                                                 (fun ps  ->
                                                                    let r1 =
                                                                    let uu____5471
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71  in
                                                                    FStar_Tactics_Monad.run_safe
                                                                    uu____5471
                                                                    ps  in
                                                                    let uu____5474
                                                                    =
                                                                    let uu____5475
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result_nbe
                                                                    er  in
                                                                    FStar_TypeChecker_NBETerm.embed
                                                                    uu____5475
                                                                    cb r1  in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____5474))))))))
                        | uu____5482 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_8 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r FStar_Tactics_Monad.tac)
        ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    't7 FStar_TypeChecker_NBETerm.embedding ->
                      't8 FStar_TypeChecker_NBETerm.embedding ->
                        'r FStar_TypeChecker_NBETerm.embedding ->
                          FStar_TypeChecker_NBETerm.args ->
                            FStar_TypeChecker_NBETerm.t
                              FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun e7  ->
                    fun e8  ->
                      fun er  ->
                        fun args  ->
                          match args with
                          | (a1,uu____5678)::(a2,uu____5680)::(a3,uu____5682)::
                              (a4,uu____5684)::(a5,uu____5686)::(a6,uu____5688)::
                              (a7,uu____5690)::(a8,uu____5692)::(a9,uu____5694)::[]
                              ->
                              let uu____5735 =
                                FStar_TypeChecker_NBETerm.unembed e1 cb a1
                                 in
                              FStar_Util.bind_opt uu____5735
                                (fun a11  ->
                                   let uu____5741 =
                                     FStar_TypeChecker_NBETerm.unembed e2 cb
                                       a2
                                      in
                                   FStar_Util.bind_opt uu____5741
                                     (fun a21  ->
                                        let uu____5747 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            e3 cb a3
                                           in
                                        FStar_Util.bind_opt uu____5747
                                          (fun a31  ->
                                             let uu____5753 =
                                               FStar_TypeChecker_NBETerm.unembed
                                                 e4 cb a4
                                                in
                                             FStar_Util.bind_opt uu____5753
                                               (fun a41  ->
                                                  let uu____5759 =
                                                    FStar_TypeChecker_NBETerm.unembed
                                                      e5 cb a5
                                                     in
                                                  FStar_Util.bind_opt
                                                    uu____5759
                                                    (fun a51  ->
                                                       let uu____5765 =
                                                         FStar_TypeChecker_NBETerm.unembed
                                                           e6 cb a6
                                                          in
                                                       FStar_Util.bind_opt
                                                         uu____5765
                                                         (fun a61  ->
                                                            let uu____5771 =
                                                              FStar_TypeChecker_NBETerm.unembed
                                                                e7 cb a7
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____5771
                                                              (fun a71  ->
                                                                 let uu____5777
                                                                   =
                                                                   FStar_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____5777
                                                                   (fun a81 
                                                                    ->
                                                                    let uu____5783
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    FStar_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a9  in
                                                                    FStar_Util.bind_opt
                                                                    uu____5783
                                                                    (fun ps 
                                                                    ->
                                                                    let r1 =
                                                                    let uu____5793
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                     in
                                                                    FStar_Tactics_Monad.run_safe
                                                                    uu____5793
                                                                    ps  in
                                                                    let uu____5796
                                                                    =
                                                                    let uu____5797
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result_nbe
                                                                    er  in
                                                                    FStar_TypeChecker_NBETerm.embed
                                                                    uu____5797
                                                                    cb r1  in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____5796)))))))))
                          | uu____5804 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_9 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 't9 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r FStar_Tactics_Monad.tac)
        ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    't7 FStar_TypeChecker_NBETerm.embedding ->
                      't8 FStar_TypeChecker_NBETerm.embedding ->
                        't9 FStar_TypeChecker_NBETerm.embedding ->
                          'r FStar_TypeChecker_NBETerm.embedding ->
                            FStar_TypeChecker_NBETerm.args ->
                              FStar_TypeChecker_NBETerm.t
                                FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun e7  ->
                    fun e8  ->
                      fun e9  ->
                        fun er  ->
                          fun args  ->
                            match args with
                            | (a1,uu____6019)::(a2,uu____6021)::(a3,uu____6023)::
                                (a4,uu____6025)::(a5,uu____6027)::(a6,uu____6029)::
                                (a7,uu____6031)::(a8,uu____6033)::(a9,uu____6035)::
                                (a10,uu____6037)::[] ->
                                let uu____6082 =
                                  FStar_TypeChecker_NBETerm.unembed e1 cb a1
                                   in
                                FStar_Util.bind_opt uu____6082
                                  (fun a11  ->
                                     let uu____6088 =
                                       FStar_TypeChecker_NBETerm.unembed e2
                                         cb a2
                                        in
                                     FStar_Util.bind_opt uu____6088
                                       (fun a21  ->
                                          let uu____6094 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              e3 cb a3
                                             in
                                          FStar_Util.bind_opt uu____6094
                                            (fun a31  ->
                                               let uu____6100 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   e4 cb a4
                                                  in
                                               FStar_Util.bind_opt uu____6100
                                                 (fun a41  ->
                                                    let uu____6106 =
                                                      FStar_TypeChecker_NBETerm.unembed
                                                        e5 cb a5
                                                       in
                                                    FStar_Util.bind_opt
                                                      uu____6106
                                                      (fun a51  ->
                                                         let uu____6112 =
                                                           FStar_TypeChecker_NBETerm.unembed
                                                             e6 cb a6
                                                            in
                                                         FStar_Util.bind_opt
                                                           uu____6112
                                                           (fun a61  ->
                                                              let uu____6118
                                                                =
                                                                FStar_TypeChecker_NBETerm.unembed
                                                                  e7 cb a7
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____6118
                                                                (fun a71  ->
                                                                   let uu____6124
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8
                                                                     in
                                                                   FStar_Util.bind_opt
                                                                    uu____6124
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____6130
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____6130
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____6136
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    FStar_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a10
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____6136
                                                                    (fun ps 
                                                                    ->
                                                                    let r1 =
                                                                    let uu____6146
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91  in
                                                                    FStar_Tactics_Monad.run_safe
                                                                    uu____6146
                                                                    ps  in
                                                                    let uu____6149
                                                                    =
                                                                    let uu____6150
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result_nbe
                                                                    er  in
                                                                    FStar_TypeChecker_NBETerm.embed
                                                                    uu____6150
                                                                    cb r1  in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____6149))))))))))
                            | uu____6157 -> FStar_Pervasives_Native.None
  
let mk_tactic_nbe_interpretation_10 :
  'r 't1 't10 't2 't3 't4 't5 't6 't7 't8 't9 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 -> 't8 -> 't9 -> 't10 -> 'r FStar_Tactics_Monad.tac)
        ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    't7 FStar_TypeChecker_NBETerm.embedding ->
                      't8 FStar_TypeChecker_NBETerm.embedding ->
                        't9 FStar_TypeChecker_NBETerm.embedding ->
                          't10 FStar_TypeChecker_NBETerm.embedding ->
                            'r FStar_TypeChecker_NBETerm.embedding ->
                              FStar_TypeChecker_NBETerm.args ->
                                FStar_TypeChecker_NBETerm.t
                                  FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun e7  ->
                    fun e8  ->
                      fun e9  ->
                        fun e10  ->
                          fun er  ->
                            fun args  ->
                              match args with
                              | (a1,uu____6391)::(a2,uu____6393)::(a3,uu____6395)::
                                  (a4,uu____6397)::(a5,uu____6399)::(a6,uu____6401)::
                                  (a7,uu____6403)::(a8,uu____6405)::(a9,uu____6407)::
                                  (a10,uu____6409)::(a11,uu____6411)::[] ->
                                  let uu____6460 =
                                    FStar_TypeChecker_NBETerm.unembed e1 cb
                                      a1
                                     in
                                  FStar_Util.bind_opt uu____6460
                                    (fun a12  ->
                                       let uu____6466 =
                                         FStar_TypeChecker_NBETerm.unembed e2
                                           cb a2
                                          in
                                       FStar_Util.bind_opt uu____6466
                                         (fun a21  ->
                                            let uu____6472 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                e3 cb a3
                                               in
                                            FStar_Util.bind_opt uu____6472
                                              (fun a31  ->
                                                 let uu____6478 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     e4 cb a4
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____6478
                                                   (fun a41  ->
                                                      let uu____6484 =
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          e5 cb a5
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____6484
                                                        (fun a51  ->
                                                           let uu____6490 =
                                                             FStar_TypeChecker_NBETerm.unembed
                                                               e6 cb a6
                                                              in
                                                           FStar_Util.bind_opt
                                                             uu____6490
                                                             (fun a61  ->
                                                                let uu____6496
                                                                  =
                                                                  FStar_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7
                                                                   in
                                                                FStar_Util.bind_opt
                                                                  uu____6496
                                                                  (fun a71 
                                                                    ->
                                                                    let uu____6502
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____6502
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____6508
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____6508
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____6514
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10  in
                                                                    FStar_Util.bind_opt
                                                                    uu____6514
                                                                    (fun a101
                                                                     ->
                                                                    let uu____6520
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    FStar_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a11
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____6520
                                                                    (fun ps 
                                                                    ->
                                                                    let r1 =
                                                                    let uu____6530
                                                                    =
                                                                    t a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                     in
                                                                    FStar_Tactics_Monad.run_safe
                                                                    uu____6530
                                                                    ps  in
                                                                    let uu____6533
                                                                    =
                                                                    let uu____6534
                                                                    =
                                                                    FStar_Tactics_Embedding.e_result_nbe
                                                                    er  in
                                                                    FStar_TypeChecker_NBETerm.embed
                                                                    uu____6534
                                                                    cb r1  in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____6533)))))))))))
                              | uu____6541 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_1 :
  'r 't1 .
    ('t1 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        'r FStar_Syntax_Embeddings.embedding ->
          FStar_TypeChecker_Cfg.psc ->
            FStar_Syntax_Embeddings.norm_cb ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun er  ->
        fun psc  ->
          fun ncb  ->
            fun args  ->
              match args with
              | (a1,uu____6609)::[] ->
                  let uu____6634 = unembed e1 a1 ncb  in
                  FStar_Util.bind_opt uu____6634
                    (fun a11  ->
                       let r1 = f a11  in
                       let uu____6642 =
                         let uu____6643 = FStar_TypeChecker_Cfg.psc_range psc
                            in
                         embed er uu____6643 r1 ncb  in
                       FStar_Pervasives_Native.Some uu____6642)
              | uu____6644 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_2 :
  'r 't1 't2 .
    ('t1 -> 't2 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_TypeChecker_Cfg.psc ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun e2  ->
        fun er  ->
          fun psc  ->
            fun ncb  ->
              fun args  ->
                match args with
                | (a1,uu____6731)::(a2,uu____6733)::[] ->
                    let uu____6774 = unembed e1 a1 ncb  in
                    FStar_Util.bind_opt uu____6774
                      (fun a11  ->
                         let uu____6780 = unembed e2 a2 ncb  in
                         FStar_Util.bind_opt uu____6780
                           (fun a21  ->
                              let r1 = f a11 a21  in
                              let uu____6788 =
                                let uu____6789 =
                                  FStar_TypeChecker_Cfg.psc_range psc  in
                                embed er uu____6789 r1 ncb  in
                              FStar_Pervasives_Native.Some uu____6788))
                | uu____6790 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_3 :
  'r 't1 't2 't3 .
    ('t1 -> 't2 -> 't3 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_TypeChecker_Cfg.psc ->
                FStar_Syntax_Embeddings.norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun er  ->
            fun psc  ->
              fun ncb  ->
                fun args  ->
                  match args with
                  | (a1,uu____6896)::(a2,uu____6898)::(a3,uu____6900)::[] ->
                      let uu____6957 = unembed e1 a1 ncb  in
                      FStar_Util.bind_opt uu____6957
                        (fun a11  ->
                           let uu____6963 = unembed e2 a2 ncb  in
                           FStar_Util.bind_opt uu____6963
                             (fun a21  ->
                                let uu____6969 = unembed e3 a3 ncb  in
                                FStar_Util.bind_opt uu____6969
                                  (fun a31  ->
                                     let r1 = f a11 a21 a31  in
                                     let uu____6977 =
                                       let uu____6978 =
                                         FStar_TypeChecker_Cfg.psc_range psc
                                          in
                                       embed er uu____6978 r1 ncb  in
                                     FStar_Pervasives_Native.Some uu____6977)))
                  | uu____6979 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_4 :
  'r 't1 't2 't3 't4 .
    ('t1 -> 't2 -> 't3 -> 't4 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                FStar_TypeChecker_Cfg.psc ->
                  FStar_Syntax_Embeddings.norm_cb ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun er  ->
              fun psc  ->
                fun ncb  ->
                  fun args  ->
                    match args with
                    | (a1,uu____7104)::(a2,uu____7106)::(a3,uu____7108)::
                        (a4,uu____7110)::[] ->
                        let uu____7183 = unembed e1 a1 ncb  in
                        FStar_Util.bind_opt uu____7183
                          (fun a11  ->
                             let uu____7189 = unembed e2 a2 ncb  in
                             FStar_Util.bind_opt uu____7189
                               (fun a21  ->
                                  let uu____7195 = unembed e3 a3 ncb  in
                                  FStar_Util.bind_opt uu____7195
                                    (fun a31  ->
                                       let uu____7201 = unembed e4 a4 ncb  in
                                       FStar_Util.bind_opt uu____7201
                                         (fun a41  ->
                                            let r1 = f a11 a21 a31 a41  in
                                            let uu____7209 =
                                              let uu____7210 =
                                                FStar_TypeChecker_Cfg.psc_range
                                                  psc
                                                 in
                                              embed er uu____7210 r1 ncb  in
                                            FStar_Pervasives_Native.Some
                                              uu____7209))))
                    | uu____7211 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_5 :
  'r 't1 't2 't3 't4 't5 .
    ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              't5 FStar_Syntax_Embeddings.embedding ->
                'r FStar_Syntax_Embeddings.embedding ->
                  FStar_TypeChecker_Cfg.psc ->
                    FStar_Syntax_Embeddings.norm_cb ->
                      FStar_Syntax_Syntax.args ->
                        FStar_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun er  ->
                fun psc  ->
                  fun ncb  ->
                    fun args  ->
                      match args with
                      | (a1,uu____7355)::(a2,uu____7357)::(a3,uu____7359)::
                          (a4,uu____7361)::(a5,uu____7363)::[] ->
                          let uu____7452 = unembed e1 a1 ncb  in
                          FStar_Util.bind_opt uu____7452
                            (fun a11  ->
                               let uu____7458 = unembed e2 a2 ncb  in
                               FStar_Util.bind_opt uu____7458
                                 (fun a21  ->
                                    let uu____7464 = unembed e3 a3 ncb  in
                                    FStar_Util.bind_opt uu____7464
                                      (fun a31  ->
                                         let uu____7470 = unembed e4 a4 ncb
                                            in
                                         FStar_Util.bind_opt uu____7470
                                           (fun a41  ->
                                              let uu____7476 =
                                                unembed e5 a5 ncb  in
                                              FStar_Util.bind_opt uu____7476
                                                (fun a51  ->
                                                   let r1 =
                                                     f a11 a21 a31 a41 a51
                                                      in
                                                   let uu____7484 =
                                                     let uu____7485 =
                                                       FStar_TypeChecker_Cfg.psc_range
                                                         psc
                                                        in
                                                     embed er uu____7485 r1
                                                       ncb
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____7484)))))
                      | uu____7486 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_6 :
  'r 't1 't2 't3 't4 't5 't6 .
    ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              't5 FStar_Syntax_Embeddings.embedding ->
                't6 FStar_Syntax_Embeddings.embedding ->
                  'r FStar_Syntax_Embeddings.embedding ->
                    FStar_TypeChecker_Cfg.psc ->
                      FStar_Syntax_Embeddings.norm_cb ->
                        FStar_Syntax_Syntax.args ->
                          FStar_Syntax_Syntax.term
                            FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun er  ->
                  fun psc  ->
                    fun ncb  ->
                      fun args  ->
                        match args with
                        | (a1,uu____7649)::(a2,uu____7651)::(a3,uu____7653)::
                            (a4,uu____7655)::(a5,uu____7657)::(a6,uu____7659)::[]
                            ->
                            let uu____7764 = unembed e1 a1 ncb  in
                            FStar_Util.bind_opt uu____7764
                              (fun a11  ->
                                 let uu____7770 = unembed e2 a2 ncb  in
                                 FStar_Util.bind_opt uu____7770
                                   (fun a21  ->
                                      let uu____7776 = unembed e3 a3 ncb  in
                                      FStar_Util.bind_opt uu____7776
                                        (fun a31  ->
                                           let uu____7782 = unembed e4 a4 ncb
                                              in
                                           FStar_Util.bind_opt uu____7782
                                             (fun a41  ->
                                                let uu____7788 =
                                                  unembed e5 a5 ncb  in
                                                FStar_Util.bind_opt
                                                  uu____7788
                                                  (fun a51  ->
                                                     let uu____7794 =
                                                       unembed e6 a6 ncb  in
                                                     FStar_Util.bind_opt
                                                       uu____7794
                                                       (fun a61  ->
                                                          let r1 =
                                                            f a11 a21 a31 a41
                                                              a51 a61
                                                             in
                                                          let uu____7802 =
                                                            let uu____7803 =
                                                              FStar_TypeChecker_Cfg.psc_range
                                                                psc
                                                               in
                                                            embed er
                                                              uu____7803 r1
                                                              ncb
                                                             in
                                                          FStar_Pervasives_Native.Some
                                                            uu____7802))))))
                        | uu____7804 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_7 :
  'r 't1 't2 't3 't4 't5 't6 't7 .
    ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              't5 FStar_Syntax_Embeddings.embedding ->
                't6 FStar_Syntax_Embeddings.embedding ->
                  't7 FStar_Syntax_Embeddings.embedding ->
                    'r FStar_Syntax_Embeddings.embedding ->
                      FStar_TypeChecker_Cfg.psc ->
                        FStar_Syntax_Embeddings.norm_cb ->
                          FStar_Syntax_Syntax.args ->
                            FStar_Syntax_Syntax.term
                              FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun e7  ->
                  fun er  ->
                    fun psc  ->
                      fun ncb  ->
                        fun args  ->
                          match args with
                          | (a1,uu____7986)::(a2,uu____7988)::(a3,uu____7990)::
                              (a4,uu____7992)::(a5,uu____7994)::(a6,uu____7996)::
                              (a7,uu____7998)::[] ->
                              let uu____8119 = unembed e1 a1 ncb  in
                              FStar_Util.bind_opt uu____8119
                                (fun a11  ->
                                   let uu____8125 = unembed e2 a2 ncb  in
                                   FStar_Util.bind_opt uu____8125
                                     (fun a21  ->
                                        let uu____8131 = unembed e3 a3 ncb
                                           in
                                        FStar_Util.bind_opt uu____8131
                                          (fun a31  ->
                                             let uu____8137 =
                                               unembed e4 a4 ncb  in
                                             FStar_Util.bind_opt uu____8137
                                               (fun a41  ->
                                                  let uu____8143 =
                                                    unembed e5 a5 ncb  in
                                                  FStar_Util.bind_opt
                                                    uu____8143
                                                    (fun a51  ->
                                                       let uu____8149 =
                                                         unembed e6 a6 ncb
                                                          in
                                                       FStar_Util.bind_opt
                                                         uu____8149
                                                         (fun a61  ->
                                                            let uu____8155 =
                                                              unembed e7 a7
                                                                ncb
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____8155
                                                              (fun a71  ->
                                                                 let r1 =
                                                                   f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71
                                                                    in
                                                                 let uu____8163
                                                                   =
                                                                   let uu____8164
                                                                    =
                                                                    FStar_TypeChecker_Cfg.psc_range
                                                                    psc  in
                                                                   embed er
                                                                    uu____8164
                                                                    r1 ncb
                                                                    in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____8163)))))))
                          | uu____8165 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_8 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 .
    ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              't5 FStar_Syntax_Embeddings.embedding ->
                't6 FStar_Syntax_Embeddings.embedding ->
                  't7 FStar_Syntax_Embeddings.embedding ->
                    't8 FStar_Syntax_Embeddings.embedding ->
                      'r FStar_Syntax_Embeddings.embedding ->
                        FStar_TypeChecker_Cfg.psc ->
                          FStar_Syntax_Embeddings.norm_cb ->
                            FStar_Syntax_Syntax.args ->
                              FStar_Syntax_Syntax.term
                                FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun e7  ->
                  fun e8  ->
                    fun er  ->
                      fun psc  ->
                        fun ncb  ->
                          fun args  ->
                            match args with
                            | (a1,uu____8366)::(a2,uu____8368)::(a3,uu____8370)::
                                (a4,uu____8372)::(a5,uu____8374)::(a6,uu____8376)::
                                (a7,uu____8378)::(a8,uu____8380)::[] ->
                                let uu____8517 = unembed e1 a1 ncb  in
                                FStar_Util.bind_opt uu____8517
                                  (fun a11  ->
                                     let uu____8523 = unembed e2 a2 ncb  in
                                     FStar_Util.bind_opt uu____8523
                                       (fun a21  ->
                                          let uu____8529 = unembed e3 a3 ncb
                                             in
                                          FStar_Util.bind_opt uu____8529
                                            (fun a31  ->
                                               let uu____8535 =
                                                 unembed e4 a4 ncb  in
                                               FStar_Util.bind_opt uu____8535
                                                 (fun a41  ->
                                                    let uu____8541 =
                                                      unembed e5 a5 ncb  in
                                                    FStar_Util.bind_opt
                                                      uu____8541
                                                      (fun a51  ->
                                                         let uu____8547 =
                                                           unembed e6 a6 ncb
                                                            in
                                                         FStar_Util.bind_opt
                                                           uu____8547
                                                           (fun a61  ->
                                                              let uu____8553
                                                                =
                                                                unembed e7 a7
                                                                  ncb
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____8553
                                                                (fun a71  ->
                                                                   let uu____8559
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb
                                                                     in
                                                                   FStar_Util.bind_opt
                                                                    uu____8559
                                                                    (fun a81 
                                                                    ->
                                                                    let r1 =
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                     in
                                                                    let uu____8567
                                                                    =
                                                                    let uu____8568
                                                                    =
                                                                    FStar_TypeChecker_Cfg.psc_range
                                                                    psc  in
                                                                    embed er
                                                                    uu____8568
                                                                    r1 ncb
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____8567))))))))
                            | uu____8569 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_9 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 't9 .
    ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r) ->
      't1 FStar_Syntax_Embeddings.embedding ->
        't2 FStar_Syntax_Embeddings.embedding ->
          't3 FStar_Syntax_Embeddings.embedding ->
            't4 FStar_Syntax_Embeddings.embedding ->
              't5 FStar_Syntax_Embeddings.embedding ->
                't6 FStar_Syntax_Embeddings.embedding ->
                  't7 FStar_Syntax_Embeddings.embedding ->
                    't8 FStar_Syntax_Embeddings.embedding ->
                      't9 FStar_Syntax_Embeddings.embedding ->
                        'r FStar_Syntax_Embeddings.embedding ->
                          FStar_TypeChecker_Cfg.psc ->
                            FStar_Syntax_Embeddings.norm_cb ->
                              FStar_Syntax_Syntax.args ->
                                FStar_Syntax_Syntax.term
                                  FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun e7  ->
                  fun e8  ->
                    fun e9  ->
                      fun er  ->
                        fun psc  ->
                          fun ncb  ->
                            fun args  ->
                              match args with
                              | (a1,uu____8789)::(a2,uu____8791)::(a3,uu____8793)::
                                  (a4,uu____8795)::(a5,uu____8797)::(a6,uu____8799)::
                                  (a7,uu____8801)::(a8,uu____8803)::(a9,uu____8805)::[]
                                  ->
                                  let uu____8958 = unembed e1 a1 ncb  in
                                  FStar_Util.bind_opt uu____8958
                                    (fun a11  ->
                                       let uu____8964 = unembed e2 a2 ncb  in
                                       FStar_Util.bind_opt uu____8964
                                         (fun a21  ->
                                            let uu____8970 =
                                              unembed e3 a3 ncb  in
                                            FStar_Util.bind_opt uu____8970
                                              (fun a31  ->
                                                 let uu____8976 =
                                                   unembed e4 a4 ncb  in
                                                 FStar_Util.bind_opt
                                                   uu____8976
                                                   (fun a41  ->
                                                      let uu____8982 =
                                                        unembed e5 a5 ncb  in
                                                      FStar_Util.bind_opt
                                                        uu____8982
                                                        (fun a51  ->
                                                           let uu____8988 =
                                                             unembed e6 a6
                                                               ncb
                                                              in
                                                           FStar_Util.bind_opt
                                                             uu____8988
                                                             (fun a61  ->
                                                                let uu____8994
                                                                  =
                                                                  unembed e7
                                                                    a7 ncb
                                                                   in
                                                                FStar_Util.bind_opt
                                                                  uu____8994
                                                                  (fun a71 
                                                                    ->
                                                                    let uu____9000
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____9000
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____9006
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____9006
                                                                    (fun a91 
                                                                    ->
                                                                    let r1 =
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91  in
                                                                    let uu____9014
                                                                    =
                                                                    let uu____9015
                                                                    =
                                                                    FStar_TypeChecker_Cfg.psc_range
                                                                    psc  in
                                                                    embed er
                                                                    uu____9015
                                                                    r1 ncb
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9014)))))))))
                              | uu____9016 -> FStar_Pervasives_Native.None
  
let mk_total_interpretation_10 :
  'r 't1 't10 't2 't3 't4 't5 't6 't7 't8 't9 .
    ('t1 ->
       't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r)
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
                          'r FStar_Syntax_Embeddings.embedding ->
                            FStar_TypeChecker_Cfg.psc ->
                              FStar_Syntax_Embeddings.norm_cb ->
                                FStar_Syntax_Syntax.args ->
                                  FStar_Syntax_Syntax.term
                                    FStar_Pervasives_Native.option
  =
  fun f  ->
    fun e1  ->
      fun e2  ->
        fun e3  ->
          fun e4  ->
            fun e5  ->
              fun e6  ->
                fun e7  ->
                  fun e8  ->
                    fun e9  ->
                      fun e10  ->
                        fun er  ->
                          fun psc  ->
                            fun ncb  ->
                              fun args  ->
                                match args with
                                | (a1,uu____9255)::(a2,uu____9257)::(a3,uu____9259)::
                                    (a4,uu____9261)::(a5,uu____9263)::
                                    (a6,uu____9265)::(a7,uu____9267)::
                                    (a8,uu____9269)::(a9,uu____9271)::
                                    (a10,uu____9273)::[] ->
                                    let uu____9442 = unembed e1 a1 ncb  in
                                    FStar_Util.bind_opt uu____9442
                                      (fun a11  ->
                                         let uu____9448 = unembed e2 a2 ncb
                                            in
                                         FStar_Util.bind_opt uu____9448
                                           (fun a21  ->
                                              let uu____9454 =
                                                unembed e3 a3 ncb  in
                                              FStar_Util.bind_opt uu____9454
                                                (fun a31  ->
                                                   let uu____9460 =
                                                     unembed e4 a4 ncb  in
                                                   FStar_Util.bind_opt
                                                     uu____9460
                                                     (fun a41  ->
                                                        let uu____9466 =
                                                          unembed e5 a5 ncb
                                                           in
                                                        FStar_Util.bind_opt
                                                          uu____9466
                                                          (fun a51  ->
                                                             let uu____9472 =
                                                               unembed e6 a6
                                                                 ncb
                                                                in
                                                             FStar_Util.bind_opt
                                                               uu____9472
                                                               (fun a61  ->
                                                                  let uu____9478
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb
                                                                     in
                                                                  FStar_Util.bind_opt
                                                                    uu____9478
                                                                    (
                                                                    fun a71 
                                                                    ->
                                                                    let uu____9484
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____9484
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____9490
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____9490
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____9496
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb  in
                                                                    FStar_Util.bind_opt
                                                                    uu____9496
                                                                    (fun a101
                                                                     ->
                                                                    let r1 =
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                     in
                                                                    let uu____9504
                                                                    =
                                                                    let uu____9505
                                                                    =
                                                                    FStar_TypeChecker_Cfg.psc_range
                                                                    psc  in
                                                                    embed er
                                                                    uu____9505
                                                                    r1 ncb
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9504))))))))))
                                | uu____9506 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_1 :
  'r 't1 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.args ->
              FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun er  ->
          fun args  ->
            match args with
            | (a1,uu____9565)::[] ->
                let uu____9574 = FStar_TypeChecker_NBETerm.unembed e1 cb a1
                   in
                FStar_Util.bind_opt uu____9574
                  (fun a11  ->
                     let r1 = f a11  in
                     let uu____9582 =
                       FStar_TypeChecker_NBETerm.embed er cb r1  in
                     FStar_Pervasives_Native.Some uu____9582)
            | uu____9583 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_2 :
  'r 't1 't2 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            'r FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.args ->
                FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun e2  ->
          fun er  ->
            fun args  ->
              match args with
              | (a1,uu____9661)::(a2,uu____9663)::[] ->
                  let uu____9676 = FStar_TypeChecker_NBETerm.unembed e1 cb a1
                     in
                  FStar_Util.bind_opt uu____9676
                    (fun a11  ->
                       let uu____9682 =
                         FStar_TypeChecker_NBETerm.unembed e2 cb a2  in
                       FStar_Util.bind_opt uu____9682
                         (fun a21  ->
                            let r1 = f a11 a21  in
                            let uu____9690 =
                              FStar_TypeChecker_NBETerm.embed er cb r1  in
                            FStar_Pervasives_Native.Some uu____9690))
              | uu____9691 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_3 :
  'r 't1 't2 't3 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              'r FStar_TypeChecker_NBETerm.embedding ->
                FStar_TypeChecker_NBETerm.args ->
                  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun er  ->
              fun args  ->
                match args with
                | (a1,uu____9788)::(a2,uu____9790)::(a3,uu____9792)::[] ->
                    let uu____9809 =
                      FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                    FStar_Util.bind_opt uu____9809
                      (fun a11  ->
                         let uu____9815 =
                           FStar_TypeChecker_NBETerm.unembed e2 cb a2  in
                         FStar_Util.bind_opt uu____9815
                           (fun a21  ->
                              let uu____9821 =
                                FStar_TypeChecker_NBETerm.unembed e3 cb a3
                                 in
                              FStar_Util.bind_opt uu____9821
                                (fun a31  ->
                                   let r1 = f a11 a21 a31  in
                                   let uu____9829 =
                                     FStar_TypeChecker_NBETerm.embed er cb r1
                                      in
                                   FStar_Pervasives_Native.Some uu____9829)))
                | uu____9830 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_4 :
  'r 't1 't2 't3 't4 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                'r FStar_TypeChecker_NBETerm.embedding ->
                  FStar_TypeChecker_NBETerm.args ->
                    FStar_TypeChecker_NBETerm.t
                      FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun er  ->
                fun args  ->
                  match args with
                  | (a1,uu____9946)::(a2,uu____9948)::(a3,uu____9950)::
                      (a4,uu____9952)::[] ->
                      let uu____9973 =
                        FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                      FStar_Util.bind_opt uu____9973
                        (fun a11  ->
                           let uu____9979 =
                             FStar_TypeChecker_NBETerm.unembed e2 cb a2  in
                           FStar_Util.bind_opt uu____9979
                             (fun a21  ->
                                let uu____9985 =
                                  FStar_TypeChecker_NBETerm.unembed e3 cb a3
                                   in
                                FStar_Util.bind_opt uu____9985
                                  (fun a31  ->
                                     let uu____9991 =
                                       FStar_TypeChecker_NBETerm.unembed e4
                                         cb a4
                                        in
                                     FStar_Util.bind_opt uu____9991
                                       (fun a41  ->
                                          let r1 = f a11 a21 a31 a41  in
                                          let uu____9999 =
                                            FStar_TypeChecker_NBETerm.embed
                                              er cb r1
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____9999))))
                  | uu____10000 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_5 :
  'r 't1 't2 't3 't4 't5 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  'r FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_NBETerm.args ->
                      FStar_TypeChecker_NBETerm.t
                        FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun er  ->
                  fun args  ->
                    match args with
                    | (a1,uu____10135)::(a2,uu____10137)::(a3,uu____10139)::
                        (a4,uu____10141)::(a5,uu____10143)::[] ->
                        let uu____10168 =
                          FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                        FStar_Util.bind_opt uu____10168
                          (fun a11  ->
                             let uu____10174 =
                               FStar_TypeChecker_NBETerm.unembed e2 cb a2  in
                             FStar_Util.bind_opt uu____10174
                               (fun a21  ->
                                  let uu____10180 =
                                    FStar_TypeChecker_NBETerm.unembed e3 cb
                                      a3
                                     in
                                  FStar_Util.bind_opt uu____10180
                                    (fun a31  ->
                                       let uu____10186 =
                                         FStar_TypeChecker_NBETerm.unembed e4
                                           cb a4
                                          in
                                       FStar_Util.bind_opt uu____10186
                                         (fun a41  ->
                                            let uu____10192 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                e5 cb a5
                                               in
                                            FStar_Util.bind_opt uu____10192
                                              (fun a51  ->
                                                 let r1 =
                                                   f a11 a21 a31 a41 a51  in
                                                 let uu____10200 =
                                                   FStar_TypeChecker_NBETerm.embed
                                                     er cb r1
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____10200)))))
                    | uu____10201 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_6 :
  'r 't1 't2 't3 't4 't5 't6 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    'r FStar_TypeChecker_NBETerm.embedding ->
                      FStar_TypeChecker_NBETerm.args ->
                        FStar_TypeChecker_NBETerm.t
                          FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun er  ->
                    fun args  ->
                      match args with
                      | (a1,uu____10355)::(a2,uu____10357)::(a3,uu____10359)::
                          (a4,uu____10361)::(a5,uu____10363)::(a6,uu____10365)::[]
                          ->
                          let uu____10394 =
                            FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                          FStar_Util.bind_opt uu____10394
                            (fun a11  ->
                               let uu____10400 =
                                 FStar_TypeChecker_NBETerm.unembed e2 cb a2
                                  in
                               FStar_Util.bind_opt uu____10400
                                 (fun a21  ->
                                    let uu____10406 =
                                      FStar_TypeChecker_NBETerm.unembed e3 cb
                                        a3
                                       in
                                    FStar_Util.bind_opt uu____10406
                                      (fun a31  ->
                                         let uu____10412 =
                                           FStar_TypeChecker_NBETerm.unembed
                                             e4 cb a4
                                            in
                                         FStar_Util.bind_opt uu____10412
                                           (fun a41  ->
                                              let uu____10418 =
                                                FStar_TypeChecker_NBETerm.unembed
                                                  e5 cb a5
                                                 in
                                              FStar_Util.bind_opt uu____10418
                                                (fun a51  ->
                                                   let uu____10424 =
                                                     FStar_TypeChecker_NBETerm.unembed
                                                       e6 cb a6
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____10424
                                                     (fun a61  ->
                                                        let r1 =
                                                          f a11 a21 a31 a41
                                                            a51 a61
                                                           in
                                                        let uu____10432 =
                                                          FStar_TypeChecker_NBETerm.embed
                                                            er cb r1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____10432))))))
                      | uu____10433 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_7 :
  'r 't1 't2 't3 't4 't5 't6 't7 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    't7 FStar_TypeChecker_NBETerm.embedding ->
                      'r FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_NBETerm.args ->
                          FStar_TypeChecker_NBETerm.t
                            FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun e7  ->
                    fun er  ->
                      fun args  ->
                        match args with
                        | (a1,uu____10606)::(a2,uu____10608)::(a3,uu____10610)::
                            (a4,uu____10612)::(a5,uu____10614)::(a6,uu____10616)::
                            (a7,uu____10618)::[] ->
                            let uu____10651 =
                              FStar_TypeChecker_NBETerm.unembed e1 cb a1  in
                            FStar_Util.bind_opt uu____10651
                              (fun a11  ->
                                 let uu____10657 =
                                   FStar_TypeChecker_NBETerm.unembed e2 cb a2
                                    in
                                 FStar_Util.bind_opt uu____10657
                                   (fun a21  ->
                                      let uu____10663 =
                                        FStar_TypeChecker_NBETerm.unembed e3
                                          cb a3
                                         in
                                      FStar_Util.bind_opt uu____10663
                                        (fun a31  ->
                                           let uu____10669 =
                                             FStar_TypeChecker_NBETerm.unembed
                                               e4 cb a4
                                              in
                                           FStar_Util.bind_opt uu____10669
                                             (fun a41  ->
                                                let uu____10675 =
                                                  FStar_TypeChecker_NBETerm.unembed
                                                    e5 cb a5
                                                   in
                                                FStar_Util.bind_opt
                                                  uu____10675
                                                  (fun a51  ->
                                                     let uu____10681 =
                                                       FStar_TypeChecker_NBETerm.unembed
                                                         e6 cb a6
                                                        in
                                                     FStar_Util.bind_opt
                                                       uu____10681
                                                       (fun a61  ->
                                                          let uu____10687 =
                                                            FStar_TypeChecker_NBETerm.unembed
                                                              e7 cb a7
                                                             in
                                                          FStar_Util.bind_opt
                                                            uu____10687
                                                            (fun a71  ->
                                                               let r1 =
                                                                 f a11 a21
                                                                   a31 a41
                                                                   a51 a61
                                                                   a71
                                                                  in
                                                               let uu____10695
                                                                 =
                                                                 FStar_TypeChecker_NBETerm.embed
                                                                   er cb r1
                                                                  in
                                                               FStar_Pervasives_Native.Some
                                                                 uu____10695)))))))
                        | uu____10696 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_8 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    't7 FStar_TypeChecker_NBETerm.embedding ->
                      't8 FStar_TypeChecker_NBETerm.embedding ->
                        'r FStar_TypeChecker_NBETerm.embedding ->
                          FStar_TypeChecker_NBETerm.args ->
                            FStar_TypeChecker_NBETerm.t
                              FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun e7  ->
                    fun e8  ->
                      fun er  ->
                        fun args  ->
                          match args with
                          | (a1,uu____10888)::(a2,uu____10890)::(a3,uu____10892)::
                              (a4,uu____10894)::(a5,uu____10896)::(a6,uu____10898)::
                              (a7,uu____10900)::(a8,uu____10902)::[] ->
                              let uu____10939 =
                                FStar_TypeChecker_NBETerm.unembed e1 cb a1
                                 in
                              FStar_Util.bind_opt uu____10939
                                (fun a11  ->
                                   let uu____10945 =
                                     FStar_TypeChecker_NBETerm.unembed e2 cb
                                       a2
                                      in
                                   FStar_Util.bind_opt uu____10945
                                     (fun a21  ->
                                        let uu____10951 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            e3 cb a3
                                           in
                                        FStar_Util.bind_opt uu____10951
                                          (fun a31  ->
                                             let uu____10957 =
                                               FStar_TypeChecker_NBETerm.unembed
                                                 e4 cb a4
                                                in
                                             FStar_Util.bind_opt uu____10957
                                               (fun a41  ->
                                                  let uu____10963 =
                                                    FStar_TypeChecker_NBETerm.unembed
                                                      e5 cb a5
                                                     in
                                                  FStar_Util.bind_opt
                                                    uu____10963
                                                    (fun a51  ->
                                                       let uu____10969 =
                                                         FStar_TypeChecker_NBETerm.unembed
                                                           e6 cb a6
                                                          in
                                                       FStar_Util.bind_opt
                                                         uu____10969
                                                         (fun a61  ->
                                                            let uu____10975 =
                                                              FStar_TypeChecker_NBETerm.unembed
                                                                e7 cb a7
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____10975
                                                              (fun a71  ->
                                                                 let uu____10981
                                                                   =
                                                                   FStar_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____10981
                                                                   (fun a81 
                                                                    ->
                                                                    let r1 =
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                     in
                                                                    let uu____10989
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.embed
                                                                    er cb r1
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10989))))))))
                          | uu____10990 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_9 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 't9 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r) ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    't7 FStar_TypeChecker_NBETerm.embedding ->
                      't8 FStar_TypeChecker_NBETerm.embedding ->
                        't9 FStar_TypeChecker_NBETerm.embedding ->
                          'r FStar_TypeChecker_NBETerm.embedding ->
                            FStar_TypeChecker_NBETerm.args ->
                              FStar_TypeChecker_NBETerm.t
                                FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun e7  ->
                    fun e8  ->
                      fun e9  ->
                        fun er  ->
                          fun args  ->
                            match args with
                            | (a1,uu____11201)::(a2,uu____11203)::(a3,uu____11205)::
                                (a4,uu____11207)::(a5,uu____11209)::(a6,uu____11211)::
                                (a7,uu____11213)::(a8,uu____11215)::(a9,uu____11217)::[]
                                ->
                                let uu____11258 =
                                  FStar_TypeChecker_NBETerm.unembed e1 cb a1
                                   in
                                FStar_Util.bind_opt uu____11258
                                  (fun a11  ->
                                     let uu____11264 =
                                       FStar_TypeChecker_NBETerm.unembed e2
                                         cb a2
                                        in
                                     FStar_Util.bind_opt uu____11264
                                       (fun a21  ->
                                          let uu____11270 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              e3 cb a3
                                             in
                                          FStar_Util.bind_opt uu____11270
                                            (fun a31  ->
                                               let uu____11276 =
                                                 FStar_TypeChecker_NBETerm.unembed
                                                   e4 cb a4
                                                  in
                                               FStar_Util.bind_opt
                                                 uu____11276
                                                 (fun a41  ->
                                                    let uu____11282 =
                                                      FStar_TypeChecker_NBETerm.unembed
                                                        e5 cb a5
                                                       in
                                                    FStar_Util.bind_opt
                                                      uu____11282
                                                      (fun a51  ->
                                                         let uu____11288 =
                                                           FStar_TypeChecker_NBETerm.unembed
                                                             e6 cb a6
                                                            in
                                                         FStar_Util.bind_opt
                                                           uu____11288
                                                           (fun a61  ->
                                                              let uu____11294
                                                                =
                                                                FStar_TypeChecker_NBETerm.unembed
                                                                  e7 cb a7
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____11294
                                                                (fun a71  ->
                                                                   let uu____11300
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8
                                                                     in
                                                                   FStar_Util.bind_opt
                                                                    uu____11300
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____11306
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____11306
                                                                    (fun a91 
                                                                    ->
                                                                    let r1 =
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91  in
                                                                    let uu____11314
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.embed
                                                                    er cb r1
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11314)))))))))
                            | uu____11315 -> FStar_Pervasives_Native.None
  
let mk_total_nbe_interpretation_10 :
  'r 't1 't10 't2 't3 't4 't5 't6 't7 't8 't9 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      ('t1 ->
         't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r)
        ->
        't1 FStar_TypeChecker_NBETerm.embedding ->
          't2 FStar_TypeChecker_NBETerm.embedding ->
            't3 FStar_TypeChecker_NBETerm.embedding ->
              't4 FStar_TypeChecker_NBETerm.embedding ->
                't5 FStar_TypeChecker_NBETerm.embedding ->
                  't6 FStar_TypeChecker_NBETerm.embedding ->
                    't7 FStar_TypeChecker_NBETerm.embedding ->
                      't8 FStar_TypeChecker_NBETerm.embedding ->
                        't9 FStar_TypeChecker_NBETerm.embedding ->
                          't10 FStar_TypeChecker_NBETerm.embedding ->
                            'r FStar_TypeChecker_NBETerm.embedding ->
                              FStar_TypeChecker_NBETerm.args ->
                                FStar_TypeChecker_NBETerm.t
                                  FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun f  ->
      fun e1  ->
        fun e2  ->
          fun e3  ->
            fun e4  ->
              fun e5  ->
                fun e6  ->
                  fun e7  ->
                    fun e8  ->
                      fun e9  ->
                        fun e10  ->
                          fun er  ->
                            fun args  ->
                              match args with
                              | (a1,uu____11545)::(a2,uu____11547)::(a3,uu____11549)::
                                  (a4,uu____11551)::(a5,uu____11553)::
                                  (a6,uu____11555)::(a7,uu____11557)::
                                  (a8,uu____11559)::(a9,uu____11561)::
                                  (a10,uu____11563)::[] ->
                                  let uu____11608 =
                                    FStar_TypeChecker_NBETerm.unembed e1 cb
                                      a1
                                     in
                                  FStar_Util.bind_opt uu____11608
                                    (fun a11  ->
                                       let uu____11614 =
                                         FStar_TypeChecker_NBETerm.unembed e2
                                           cb a2
                                          in
                                       FStar_Util.bind_opt uu____11614
                                         (fun a21  ->
                                            let uu____11620 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                e3 cb a3
                                               in
                                            FStar_Util.bind_opt uu____11620
                                              (fun a31  ->
                                                 let uu____11626 =
                                                   FStar_TypeChecker_NBETerm.unembed
                                                     e4 cb a4
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____11626
                                                   (fun a41  ->
                                                      let uu____11632 =
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          e5 cb a5
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____11632
                                                        (fun a51  ->
                                                           let uu____11638 =
                                                             FStar_TypeChecker_NBETerm.unembed
                                                               e6 cb a6
                                                              in
                                                           FStar_Util.bind_opt
                                                             uu____11638
                                                             (fun a61  ->
                                                                let uu____11644
                                                                  =
                                                                  FStar_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7
                                                                   in
                                                                FStar_Util.bind_opt
                                                                  uu____11644
                                                                  (fun a71 
                                                                    ->
                                                                    let uu____11650
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____11650
                                                                    (fun a81 
                                                                    ->
                                                                    let uu____11656
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9
                                                                     in
                                                                    FStar_Util.bind_opt
                                                                    uu____11656
                                                                    (fun a91 
                                                                    ->
                                                                    let uu____11662
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10  in
                                                                    FStar_Util.bind_opt
                                                                    uu____11662
                                                                    (fun a101
                                                                     ->
                                                                    let r1 =
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                     in
                                                                    let uu____11670
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.embed
                                                                    er cb r1
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11670))))))))))
                              | uu____11671 -> FStar_Pervasives_Native.None
  
let mk_tac_step_1 :
  'nr 'nt1 'r 't1 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 'r FStar_Tactics_Monad.tac) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              ('nt1 -> 'nr FStar_Tactics_Monad.tac) ->
                'nt1 FStar_TypeChecker_NBETerm.embedding ->
                  'nr FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun t  ->
        fun e1  ->
          fun er  ->
            fun nt  ->
              fun ne1  ->
                fun ner  ->
                  mk name (Prims.of_int (2)) nunivs
                    (mk_tactic_interpretation_1 t e1 er)
                    (fun cb  ->
                       fun args  ->
                         let uu____11785 = drop nunivs args  in
                         mk_tactic_nbe_interpretation_1 cb nt ne1 ner
                           uu____11785)
  
let mk_tac_step_2 :
  'nr 'nt1 'nt2 'r 't1 't2 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 'r FStar_Tactics_Monad.tac) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                ('nt1 -> 'nt2 -> 'nr FStar_Tactics_Monad.tac) ->
                  'nt1 FStar_TypeChecker_NBETerm.embedding ->
                    'nt2 FStar_TypeChecker_NBETerm.embedding ->
                      'nr FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____11957  ->
    fun uu____11956  ->
      fun uu____11955  ->
        fun uu____11954  ->
          fun uu____11953  ->
            fun uu____11952  ->
              fun uu____11951  ->
                fun uu____11950  ->
                  fun uu____11949  ->
                    fun uu____11948  ->
                      (fun nunivs  ->
                         fun name  ->
                           fun t  ->
                             fun e1  ->
                               fun e2  ->
                                 fun er  ->
                                   fun nt  ->
                                     let nt = Obj.magic nt  in
                                     fun ne1  ->
                                       fun ne2  ->
                                         fun ner  ->
                                           Obj.magic
                                             (mk name (Prims.of_int (3))
                                                nunivs
                                                (mk_tactic_interpretation_2 t
                                                   e1 e2 er)
                                                (fun cb  ->
                                                   fun args  ->
                                                     let uu____11941 =
                                                       drop nunivs args  in
                                                     mk_tactic_nbe_interpretation_2
                                                       cb
                                                       (fun uu____11947  ->
                                                          fun uu____11946  ->
                                                            (Obj.magic nt)
                                                              uu____11947
                                                              uu____11946)
                                                       ne1 ne2 ner
                                                       uu____11941)))
                        uu____11957 uu____11956 uu____11955 uu____11954
                        uu____11953 uu____11952 uu____11951 uu____11950
                        uu____11949 uu____11948
  
let mk_tac_step_3 :
  'nr 'nt1 'nt2 'nt3 'r 't1 't2 't3 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 'r FStar_Tactics_Monad.tac) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                'r FStar_Syntax_Embeddings.embedding ->
                  ('nt1 -> 'nt2 -> 'nt3 -> 'nr FStar_Tactics_Monad.tac) ->
                    'nt1 FStar_TypeChecker_NBETerm.embedding ->
                      'nt2 FStar_TypeChecker_NBETerm.embedding ->
                        'nt3 FStar_TypeChecker_NBETerm.embedding ->
                          'nr FStar_TypeChecker_NBETerm.embedding ->
                            FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____12166  ->
    fun uu____12165  ->
      fun uu____12164  ->
        fun uu____12163  ->
          fun uu____12162  ->
            fun uu____12161  ->
              fun uu____12160  ->
                fun uu____12159  ->
                  fun uu____12158  ->
                    fun uu____12157  ->
                      fun uu____12156  ->
                        fun uu____12155  ->
                          (fun nunivs  ->
                             fun name  ->
                               fun t  ->
                                 fun e1  ->
                                   fun e2  ->
                                     fun e3  ->
                                       fun er  ->
                                         fun nt  ->
                                           let nt = Obj.magic nt  in
                                           fun ne1  ->
                                             fun ne2  ->
                                               fun ne3  ->
                                                 fun ner  ->
                                                   Obj.magic
                                                     (mk name
                                                        (Prims.of_int (4))
                                                        nunivs
                                                        (mk_tactic_interpretation_3
                                                           t e1 e2 e3 er)
                                                        (fun cb  ->
                                                           fun args  ->
                                                             let uu____12147
                                                               =
                                                               drop nunivs
                                                                 args
                                                                in
                                                             mk_tactic_nbe_interpretation_3
                                                               cb
                                                               (fun
                                                                  uu____12154
                                                                   ->
                                                                  fun
                                                                    uu____12153
                                                                     ->
                                                                    fun
                                                                    uu____12152
                                                                     ->
                                                                    (Obj.magic
                                                                    nt)
                                                                    uu____12154
                                                                    uu____12153
                                                                    uu____12152)
                                                               ne1 ne2 ne3
                                                               ner
                                                               uu____12147)))
                            uu____12166 uu____12165 uu____12164 uu____12163
                            uu____12162 uu____12161 uu____12160 uu____12159
                            uu____12158 uu____12157 uu____12156 uu____12155
  
let mk_tac_step_4 :
  'nr 'nt1 'nt2 'nt3 'nt4 'r 't1 't2 't3 't4 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 'r FStar_Tactics_Monad.tac) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  'r FStar_Syntax_Embeddings.embedding ->
                    ('nt1 ->
                       'nt2 -> 'nt3 -> 'nt4 -> 'nr FStar_Tactics_Monad.tac)
                      ->
                      'nt1 FStar_TypeChecker_NBETerm.embedding ->
                        'nt2 FStar_TypeChecker_NBETerm.embedding ->
                          'nt3 FStar_TypeChecker_NBETerm.embedding ->
                            'nt4 FStar_TypeChecker_NBETerm.embedding ->
                              'nr FStar_TypeChecker_NBETerm.embedding ->
                                FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____12416  ->
    fun uu____12415  ->
      fun uu____12414  ->
        fun uu____12413  ->
          fun uu____12412  ->
            fun uu____12411  ->
              fun uu____12410  ->
                fun uu____12409  ->
                  fun uu____12408  ->
                    fun uu____12407  ->
                      fun uu____12406  ->
                        fun uu____12405  ->
                          fun uu____12404  ->
                            fun uu____12403  ->
                              (fun nunivs  ->
                                 fun name  ->
                                   fun t  ->
                                     fun e1  ->
                                       fun e2  ->
                                         fun e3  ->
                                           fun e4  ->
                                             fun er  ->
                                               fun nt  ->
                                                 let nt = Obj.magic nt  in
                                                 fun ne1  ->
                                                   fun ne2  ->
                                                     fun ne3  ->
                                                       fun ne4  ->
                                                         fun ner  ->
                                                           Obj.magic
                                                             (mk name
                                                                (Prims.of_int (5))
                                                                nunivs
                                                                (mk_tactic_interpretation_4
                                                                   t e1 e2 e3
                                                                   e4 er)
                                                                (fun cb  ->
                                                                   fun args 
                                                                    ->
                                                                    let uu____12394
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_tactic_nbe_interpretation_4
                                                                    cb
                                                                    (fun
                                                                    uu____12402
                                                                     ->
                                                                    fun
                                                                    uu____12401
                                                                     ->
                                                                    fun
                                                                    uu____12400
                                                                     ->
                                                                    fun
                                                                    uu____12399
                                                                     ->
                                                                    (Obj.magic
                                                                    nt)
                                                                    uu____12402
                                                                    uu____12401
                                                                    uu____12400
                                                                    uu____12399)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ner
                                                                    uu____12394)))
                                uu____12416 uu____12415 uu____12414
                                uu____12413 uu____12412 uu____12411
                                uu____12410 uu____12409 uu____12408
                                uu____12407 uu____12406 uu____12405
                                uu____12404 uu____12403
  
let mk_tac_step_5 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'r 't1 't2 't3 't4 't5 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r FStar_Tactics_Monad.tac) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  't5 FStar_Syntax_Embeddings.embedding ->
                    'r FStar_Syntax_Embeddings.embedding ->
                      ('nt1 ->
                         'nt2 ->
                           'nt3 ->
                             'nt4 -> 'nt5 -> 'nr FStar_Tactics_Monad.tac)
                        ->
                        'nt1 FStar_TypeChecker_NBETerm.embedding ->
                          'nt2 FStar_TypeChecker_NBETerm.embedding ->
                            'nt3 FStar_TypeChecker_NBETerm.embedding ->
                              'nt4 FStar_TypeChecker_NBETerm.embedding ->
                                'nt5 FStar_TypeChecker_NBETerm.embedding ->
                                  'nr FStar_TypeChecker_NBETerm.embedding ->
                                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____12707  ->
    fun uu____12706  ->
      fun uu____12705  ->
        fun uu____12704  ->
          fun uu____12703  ->
            fun uu____12702  ->
              fun uu____12701  ->
                fun uu____12700  ->
                  fun uu____12699  ->
                    fun uu____12698  ->
                      fun uu____12697  ->
                        fun uu____12696  ->
                          fun uu____12695  ->
                            fun uu____12694  ->
                              fun uu____12693  ->
                                fun uu____12692  ->
                                  (fun nunivs  ->
                                     fun name  ->
                                       fun t  ->
                                         fun e1  ->
                                           fun e2  ->
                                             fun e3  ->
                                               fun e4  ->
                                                 fun e5  ->
                                                   fun er  ->
                                                     fun nt  ->
                                                       let nt = Obj.magic nt
                                                          in
                                                       fun ne1  ->
                                                         fun ne2  ->
                                                           fun ne3  ->
                                                             fun ne4  ->
                                                               fun ne5  ->
                                                                 fun ner  ->
                                                                   Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (6))
                                                                    nunivs
                                                                    (mk_tactic_interpretation_5
                                                                    t e1 e2
                                                                    e3 e4 e5
                                                                    er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____12682
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_tactic_nbe_interpretation_5
                                                                    cb
                                                                    (fun
                                                                    uu____12691
                                                                     ->
                                                                    fun
                                                                    uu____12690
                                                                     ->
                                                                    fun
                                                                    uu____12689
                                                                     ->
                                                                    fun
                                                                    uu____12688
                                                                     ->
                                                                    fun
                                                                    uu____12687
                                                                     ->
                                                                    (Obj.magic
                                                                    nt)
                                                                    uu____12691
                                                                    uu____12690
                                                                    uu____12689
                                                                    uu____12688
                                                                    uu____12687)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ner
                                                                    uu____12682)))
                                    uu____12707 uu____12706 uu____12705
                                    uu____12704 uu____12703 uu____12702
                                    uu____12701 uu____12700 uu____12699
                                    uu____12698 uu____12697 uu____12696
                                    uu____12695 uu____12694 uu____12693
                                    uu____12692
  
let mk_tac_step_6 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'nt6 'r 't1 't2 't3 't4 't5 't6 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r FStar_Tactics_Monad.tac)
          ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  't5 FStar_Syntax_Embeddings.embedding ->
                    't6 FStar_Syntax_Embeddings.embedding ->
                      'r FStar_Syntax_Embeddings.embedding ->
                        ('nt1 ->
                           'nt2 ->
                             'nt3 ->
                               'nt4 ->
                                 'nt5 -> 'nt6 -> 'nr FStar_Tactics_Monad.tac)
                          ->
                          'nt1 FStar_TypeChecker_NBETerm.embedding ->
                            'nt2 FStar_TypeChecker_NBETerm.embedding ->
                              'nt3 FStar_TypeChecker_NBETerm.embedding ->
                                'nt4 FStar_TypeChecker_NBETerm.embedding ->
                                  'nt5 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt6 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nr FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____13039  ->
    fun uu____13038  ->
      fun uu____13037  ->
        fun uu____13036  ->
          fun uu____13035  ->
            fun uu____13034  ->
              fun uu____13033  ->
                fun uu____13032  ->
                  fun uu____13031  ->
                    fun uu____13030  ->
                      fun uu____13029  ->
                        fun uu____13028  ->
                          fun uu____13027  ->
                            fun uu____13026  ->
                              fun uu____13025  ->
                                fun uu____13024  ->
                                  fun uu____13023  ->
                                    fun uu____13022  ->
                                      (fun nunivs  ->
                                         fun name  ->
                                           fun t  ->
                                             fun e1  ->
                                               fun e2  ->
                                                 fun e3  ->
                                                   fun e4  ->
                                                     fun e5  ->
                                                       fun e6  ->
                                                         fun er  ->
                                                           fun nt  ->
                                                             let nt =
                                                               Obj.magic nt
                                                                in
                                                             fun ne1  ->
                                                               fun ne2  ->
                                                                 fun ne3  ->
                                                                   fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (7))
                                                                    nunivs
                                                                    (mk_tactic_interpretation_6
                                                                    t e1 e2
                                                                    e3 e4 e5
                                                                    e6 er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____13011
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_tactic_nbe_interpretation_6
                                                                    cb
                                                                    (fun
                                                                    uu____13021
                                                                     ->
                                                                    fun
                                                                    uu____13020
                                                                     ->
                                                                    fun
                                                                    uu____13019
                                                                     ->
                                                                    fun
                                                                    uu____13018
                                                                     ->
                                                                    fun
                                                                    uu____13017
                                                                     ->
                                                                    fun
                                                                    uu____13016
                                                                     ->
                                                                    (Obj.magic
                                                                    nt)
                                                                    uu____13021
                                                                    uu____13020
                                                                    uu____13019
                                                                    uu____13018
                                                                    uu____13017
                                                                    uu____13016)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ner
                                                                    uu____13011)))
                                        uu____13039 uu____13038 uu____13037
                                        uu____13036 uu____13035 uu____13034
                                        uu____13033 uu____13032 uu____13031
                                        uu____13030 uu____13029 uu____13028
                                        uu____13027 uu____13026 uu____13025
                                        uu____13024 uu____13023 uu____13022
  
let mk_tac_step_7 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'nt6 'nt7 'r 't1 't2 't3 't4 't5 't6 't7 .
    Prims.int ->
      Prims.string ->
        ('t1 ->
           't2 ->
             't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r FStar_Tactics_Monad.tac)
          ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  't5 FStar_Syntax_Embeddings.embedding ->
                    't6 FStar_Syntax_Embeddings.embedding ->
                      't7 FStar_Syntax_Embeddings.embedding ->
                        'r FStar_Syntax_Embeddings.embedding ->
                          ('nt1 ->
                             'nt2 ->
                               'nt3 ->
                                 'nt4 ->
                                   'nt5 ->
                                     'nt6 ->
                                       'nt7 -> 'nr FStar_Tactics_Monad.tac)
                            ->
                            'nt1 FStar_TypeChecker_NBETerm.embedding ->
                              'nt2 FStar_TypeChecker_NBETerm.embedding ->
                                'nt3 FStar_TypeChecker_NBETerm.embedding ->
                                  'nt4 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt5 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nt6
                                        FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        'nt7
                                          FStar_TypeChecker_NBETerm.embedding
                                          ->
                                          'nr
                                            FStar_TypeChecker_NBETerm.embedding
                                            ->
                                            FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____13412  ->
    fun uu____13411  ->
      fun uu____13410  ->
        fun uu____13409  ->
          fun uu____13408  ->
            fun uu____13407  ->
              fun uu____13406  ->
                fun uu____13405  ->
                  fun uu____13404  ->
                    fun uu____13403  ->
                      fun uu____13402  ->
                        fun uu____13401  ->
                          fun uu____13400  ->
                            fun uu____13399  ->
                              fun uu____13398  ->
                                fun uu____13397  ->
                                  fun uu____13396  ->
                                    fun uu____13395  ->
                                      fun uu____13394  ->
                                        fun uu____13393  ->
                                          (fun nunivs  ->
                                             fun name  ->
                                               fun t  ->
                                                 fun e1  ->
                                                   fun e2  ->
                                                     fun e3  ->
                                                       fun e4  ->
                                                         fun e5  ->
                                                           fun e6  ->
                                                             fun e7  ->
                                                               fun er  ->
                                                                 fun nt  ->
                                                                   let nt =
                                                                    Obj.magic
                                                                    nt  in
                                                                   fun ne1 
                                                                    ->
                                                                    fun ne2 
                                                                    ->
                                                                    fun ne3 
                                                                    ->
                                                                    fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ne7 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (8))
                                                                    nunivs
                                                                    (mk_tactic_interpretation_7
                                                                    t e1 e2
                                                                    e3 e4 e5
                                                                    e6 e7 er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____13381
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_tactic_nbe_interpretation_7
                                                                    cb
                                                                    (fun
                                                                    uu____13392
                                                                     ->
                                                                    fun
                                                                    uu____13391
                                                                     ->
                                                                    fun
                                                                    uu____13390
                                                                     ->
                                                                    fun
                                                                    uu____13389
                                                                     ->
                                                                    fun
                                                                    uu____13388
                                                                     ->
                                                                    fun
                                                                    uu____13387
                                                                     ->
                                                                    fun
                                                                    uu____13386
                                                                     ->
                                                                    (Obj.magic
                                                                    nt)
                                                                    uu____13392
                                                                    uu____13391
                                                                    uu____13390
                                                                    uu____13389
                                                                    uu____13388
                                                                    uu____13387
                                                                    uu____13386)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ne7 ner
                                                                    uu____13381)))
                                            uu____13412 uu____13411
                                            uu____13410 uu____13409
                                            uu____13408 uu____13407
                                            uu____13406 uu____13405
                                            uu____13404 uu____13403
                                            uu____13402 uu____13401
                                            uu____13400 uu____13399
                                            uu____13398 uu____13397
                                            uu____13396 uu____13395
                                            uu____13394 uu____13393
  
let mk_tac_step_8 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'nt6 'nt7 'nt8 'r 't1 't2 't3 't4 't5 't6 't7
    't8 .
    Prims.int ->
      Prims.string ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r FStar_Tactics_Monad.tac)
          ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  't5 FStar_Syntax_Embeddings.embedding ->
                    't6 FStar_Syntax_Embeddings.embedding ->
                      't7 FStar_Syntax_Embeddings.embedding ->
                        't8 FStar_Syntax_Embeddings.embedding ->
                          'r FStar_Syntax_Embeddings.embedding ->
                            ('nt1 ->
                               'nt2 ->
                                 'nt3 ->
                                   'nt4 ->
                                     'nt5 ->
                                       'nt6 ->
                                         'nt7 ->
                                           'nt8 ->
                                             'nr FStar_Tactics_Monad.tac)
                              ->
                              'nt1 FStar_TypeChecker_NBETerm.embedding ->
                                'nt2 FStar_TypeChecker_NBETerm.embedding ->
                                  'nt3 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt4 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nt5
                                        FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        'nt6
                                          FStar_TypeChecker_NBETerm.embedding
                                          ->
                                          'nt7
                                            FStar_TypeChecker_NBETerm.embedding
                                            ->
                                            'nt8
                                              FStar_TypeChecker_NBETerm.embedding
                                              ->
                                              'nr
                                                FStar_TypeChecker_NBETerm.embedding
                                                ->
                                                FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____13826  ->
    fun uu____13825  ->
      fun uu____13824  ->
        fun uu____13823  ->
          fun uu____13822  ->
            fun uu____13821  ->
              fun uu____13820  ->
                fun uu____13819  ->
                  fun uu____13818  ->
                    fun uu____13817  ->
                      fun uu____13816  ->
                        fun uu____13815  ->
                          fun uu____13814  ->
                            fun uu____13813  ->
                              fun uu____13812  ->
                                fun uu____13811  ->
                                  fun uu____13810  ->
                                    fun uu____13809  ->
                                      fun uu____13808  ->
                                        fun uu____13807  ->
                                          fun uu____13806  ->
                                            fun uu____13805  ->
                                              (fun nunivs  ->
                                                 fun name  ->
                                                   fun t  ->
                                                     fun e1  ->
                                                       fun e2  ->
                                                         fun e3  ->
                                                           fun e4  ->
                                                             fun e5  ->
                                                               fun e6  ->
                                                                 fun e7  ->
                                                                   fun e8  ->
                                                                    fun er 
                                                                    ->
                                                                    fun nt 
                                                                    ->
                                                                    let nt =
                                                                    Obj.magic
                                                                    nt  in
                                                                    fun ne1 
                                                                    ->
                                                                    fun ne2 
                                                                    ->
                                                                    fun ne3 
                                                                    ->
                                                                    fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ne7 
                                                                    ->
                                                                    fun ne8 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (9))
                                                                    nunivs
                                                                    (mk_tactic_interpretation_8
                                                                    t e1 e2
                                                                    e3 e4 e5
                                                                    e6 e7 e8
                                                                    er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____13792
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_tactic_nbe_interpretation_8
                                                                    cb
                                                                    (fun
                                                                    uu____13804
                                                                     ->
                                                                    fun
                                                                    uu____13803
                                                                     ->
                                                                    fun
                                                                    uu____13802
                                                                     ->
                                                                    fun
                                                                    uu____13801
                                                                     ->
                                                                    fun
                                                                    uu____13800
                                                                     ->
                                                                    fun
                                                                    uu____13799
                                                                     ->
                                                                    fun
                                                                    uu____13798
                                                                     ->
                                                                    fun
                                                                    uu____13797
                                                                     ->
                                                                    (Obj.magic
                                                                    nt)
                                                                    uu____13804
                                                                    uu____13803
                                                                    uu____13802
                                                                    uu____13801
                                                                    uu____13800
                                                                    uu____13799
                                                                    uu____13798
                                                                    uu____13797)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ne7 ne8
                                                                    ner
                                                                    uu____13792)))
                                                uu____13826 uu____13825
                                                uu____13824 uu____13823
                                                uu____13822 uu____13821
                                                uu____13820 uu____13819
                                                uu____13818 uu____13817
                                                uu____13816 uu____13815
                                                uu____13814 uu____13813
                                                uu____13812 uu____13811
                                                uu____13810 uu____13809
                                                uu____13808 uu____13807
                                                uu____13806 uu____13805
  
let mk_tac_step_9 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'nt6 'nt7 'nt8 'nt9 'r 't1 't2 't3 't4 't5 't6
    't7 't8 't9 .
    Prims.int ->
      Prims.string ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 -> 't7 -> 't8 -> 't9 -> 'r FStar_Tactics_Monad.tac)
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
                            'r FStar_Syntax_Embeddings.embedding ->
                              ('nt1 ->
                                 'nt2 ->
                                   'nt3 ->
                                     'nt4 ->
                                       'nt5 ->
                                         'nt6 ->
                                           'nt7 ->
                                             'nt8 ->
                                               'nt9 ->
                                                 'nr FStar_Tactics_Monad.tac)
                                ->
                                'nt1 FStar_TypeChecker_NBETerm.embedding ->
                                  'nt2 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt3 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nt4
                                        FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        'nt5
                                          FStar_TypeChecker_NBETerm.embedding
                                          ->
                                          'nt6
                                            FStar_TypeChecker_NBETerm.embedding
                                            ->
                                            'nt7
                                              FStar_TypeChecker_NBETerm.embedding
                                              ->
                                              'nt8
                                                FStar_TypeChecker_NBETerm.embedding
                                                ->
                                                'nt9
                                                  FStar_TypeChecker_NBETerm.embedding
                                                  ->
                                                  'nr
                                                    FStar_TypeChecker_NBETerm.embedding
                                                    ->
                                                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____14281  ->
    fun uu____14280  ->
      fun uu____14279  ->
        fun uu____14278  ->
          fun uu____14277  ->
            fun uu____14276  ->
              fun uu____14275  ->
                fun uu____14274  ->
                  fun uu____14273  ->
                    fun uu____14272  ->
                      fun uu____14271  ->
                        fun uu____14270  ->
                          fun uu____14269  ->
                            fun uu____14268  ->
                              fun uu____14267  ->
                                fun uu____14266  ->
                                  fun uu____14265  ->
                                    fun uu____14264  ->
                                      fun uu____14263  ->
                                        fun uu____14262  ->
                                          fun uu____14261  ->
                                            fun uu____14260  ->
                                              fun uu____14259  ->
                                                fun uu____14258  ->
                                                  (fun nunivs  ->
                                                     fun name  ->
                                                       fun t  ->
                                                         fun e1  ->
                                                           fun e2  ->
                                                             fun e3  ->
                                                               fun e4  ->
                                                                 fun e5  ->
                                                                   fun e6  ->
                                                                    fun e7 
                                                                    ->
                                                                    fun e8 
                                                                    ->
                                                                    fun e9 
                                                                    ->
                                                                    fun er 
                                                                    ->
                                                                    fun nt 
                                                                    ->
                                                                    let nt =
                                                                    Obj.magic
                                                                    nt  in
                                                                    fun ne1 
                                                                    ->
                                                                    fun ne2 
                                                                    ->
                                                                    fun ne3 
                                                                    ->
                                                                    fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ne7 
                                                                    ->
                                                                    fun ne8 
                                                                    ->
                                                                    fun ne9 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (10))
                                                                    nunivs
                                                                    (mk_tactic_interpretation_9
                                                                    t e1 e2
                                                                    e3 e4 e5
                                                                    e6 e7 e8
                                                                    e9 er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____14244
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_tactic_nbe_interpretation_9
                                                                    cb
                                                                    (fun
                                                                    uu____14257
                                                                     ->
                                                                    fun
                                                                    uu____14256
                                                                     ->
                                                                    fun
                                                                    uu____14255
                                                                     ->
                                                                    fun
                                                                    uu____14254
                                                                     ->
                                                                    fun
                                                                    uu____14253
                                                                     ->
                                                                    fun
                                                                    uu____14252
                                                                     ->
                                                                    fun
                                                                    uu____14251
                                                                     ->
                                                                    fun
                                                                    uu____14250
                                                                     ->
                                                                    fun
                                                                    uu____14249
                                                                     ->
                                                                    (Obj.magic
                                                                    nt)
                                                                    uu____14257
                                                                    uu____14256
                                                                    uu____14255
                                                                    uu____14254
                                                                    uu____14253
                                                                    uu____14252
                                                                    uu____14251
                                                                    uu____14250
                                                                    uu____14249)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ne7 ne8
                                                                    ne9 ner
                                                                    uu____14244)))
                                                    uu____14281 uu____14280
                                                    uu____14279 uu____14278
                                                    uu____14277 uu____14276
                                                    uu____14275 uu____14274
                                                    uu____14273 uu____14272
                                                    uu____14271 uu____14270
                                                    uu____14269 uu____14268
                                                    uu____14267 uu____14266
                                                    uu____14265 uu____14264
                                                    uu____14263 uu____14262
                                                    uu____14261 uu____14260
                                                    uu____14259 uu____14258
  
let mk_tac_step_10 :
  'nr 'nt1 'nt10 'nt2 'nt3 'nt4 'nt5 'nt6 'nt7 'nt8 'nt9 'r 't1 't10 't2 't3
    't4 't5 't6 't7 't8 't9 .
    Prims.int ->
      Prims.string ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 -> 't8 -> 't9 -> 't10 -> 'r FStar_Tactics_Monad.tac)
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
                              'r FStar_Syntax_Embeddings.embedding ->
                                ('nt1 ->
                                   'nt2 ->
                                     'nt3 ->
                                       'nt4 ->
                                         'nt5 ->
                                           'nt6 ->
                                             'nt7 ->
                                               'nt8 ->
                                                 'nt9 ->
                                                   'nt10 ->
                                                     'nr
                                                       FStar_Tactics_Monad.tac)
                                  ->
                                  'nt1 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt2 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nt3
                                        FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        'nt4
                                          FStar_TypeChecker_NBETerm.embedding
                                          ->
                                          'nt5
                                            FStar_TypeChecker_NBETerm.embedding
                                            ->
                                            'nt6
                                              FStar_TypeChecker_NBETerm.embedding
                                              ->
                                              'nt7
                                                FStar_TypeChecker_NBETerm.embedding
                                                ->
                                                'nt8
                                                  FStar_TypeChecker_NBETerm.embedding
                                                  ->
                                                  'nt9
                                                    FStar_TypeChecker_NBETerm.embedding
                                                    ->
                                                    'nt10
                                                      FStar_TypeChecker_NBETerm.embedding
                                                      ->
                                                      'nr
                                                        FStar_TypeChecker_NBETerm.embedding
                                                        ->
                                                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____14777  ->
    fun uu____14776  ->
      fun uu____14775  ->
        fun uu____14774  ->
          fun uu____14773  ->
            fun uu____14772  ->
              fun uu____14771  ->
                fun uu____14770  ->
                  fun uu____14769  ->
                    fun uu____14768  ->
                      fun uu____14767  ->
                        fun uu____14766  ->
                          fun uu____14765  ->
                            fun uu____14764  ->
                              fun uu____14763  ->
                                fun uu____14762  ->
                                  fun uu____14761  ->
                                    fun uu____14760  ->
                                      fun uu____14759  ->
                                        fun uu____14758  ->
                                          fun uu____14757  ->
                                            fun uu____14756  ->
                                              fun uu____14755  ->
                                                fun uu____14754  ->
                                                  fun uu____14753  ->
                                                    fun uu____14752  ->
                                                      (fun nunivs  ->
                                                         fun name  ->
                                                           fun t  ->
                                                             fun e1  ->
                                                               fun e2  ->
                                                                 fun e3  ->
                                                                   fun e4  ->
                                                                    fun e5 
                                                                    ->
                                                                    fun e6 
                                                                    ->
                                                                    fun e7 
                                                                    ->
                                                                    fun e8 
                                                                    ->
                                                                    fun e9 
                                                                    ->
                                                                    fun e10 
                                                                    ->
                                                                    fun er 
                                                                    ->
                                                                    fun nt 
                                                                    ->
                                                                    let nt =
                                                                    Obj.magic
                                                                    nt  in
                                                                    fun ne1 
                                                                    ->
                                                                    fun ne2 
                                                                    ->
                                                                    fun ne3 
                                                                    ->
                                                                    fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ne7 
                                                                    ->
                                                                    fun ne8 
                                                                    ->
                                                                    fun ne9 
                                                                    ->
                                                                    fun ne10 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (11))
                                                                    nunivs
                                                                    (mk_tactic_interpretation_10
                                                                    t e1 e2
                                                                    e3 e4 e5
                                                                    e6 e7 e8
                                                                    e9 e10 er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____14737
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_tactic_nbe_interpretation_10
                                                                    cb
                                                                    (fun
                                                                    uu____14751
                                                                     ->
                                                                    fun
                                                                    uu____14750
                                                                     ->
                                                                    fun
                                                                    uu____14749
                                                                     ->
                                                                    fun
                                                                    uu____14748
                                                                     ->
                                                                    fun
                                                                    uu____14747
                                                                     ->
                                                                    fun
                                                                    uu____14746
                                                                     ->
                                                                    fun
                                                                    uu____14745
                                                                     ->
                                                                    fun
                                                                    uu____14744
                                                                     ->
                                                                    fun
                                                                    uu____14743
                                                                     ->
                                                                    fun
                                                                    uu____14742
                                                                     ->
                                                                    (Obj.magic
                                                                    nt)
                                                                    uu____14751
                                                                    uu____14750
                                                                    uu____14749
                                                                    uu____14748
                                                                    uu____14747
                                                                    uu____14746
                                                                    uu____14745
                                                                    uu____14744
                                                                    uu____14743
                                                                    uu____14742)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ne7 ne8
                                                                    ne9 ne10
                                                                    ner
                                                                    uu____14737)))
                                                        uu____14777
                                                        uu____14776
                                                        uu____14775
                                                        uu____14774
                                                        uu____14773
                                                        uu____14772
                                                        uu____14771
                                                        uu____14770
                                                        uu____14769
                                                        uu____14768
                                                        uu____14767
                                                        uu____14766
                                                        uu____14765
                                                        uu____14764
                                                        uu____14763
                                                        uu____14762
                                                        uu____14761
                                                        uu____14760
                                                        uu____14759
                                                        uu____14758
                                                        uu____14757
                                                        uu____14756
                                                        uu____14755
                                                        uu____14754
                                                        uu____14753
                                                        uu____14752
  
let mk_total_step_1 :
  'nr 'nt1 'r 't1 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 'r) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              ('nt1 -> 'nr) ->
                'nt1 FStar_TypeChecker_NBETerm.embedding ->
                  'nr FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun e1  ->
          fun er  ->
            fun nf  ->
              fun ne1  ->
                fun ner  ->
                  mk name (Prims.of_int (2)) nunivs
                    (mk_total_interpretation_1 f e1 er)
                    (fun cb  ->
                       fun args  ->
                         let uu____14883 = drop nunivs args  in
                         mk_total_nbe_interpretation_1 cb nf ne1 ner
                           uu____14883)
  
let mk_total_step_2 :
  'nr 'nt1 'nt2 'r 't1 't2 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 'r) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              'r FStar_Syntax_Embeddings.embedding ->
                ('nt1 -> 'nt2 -> 'nr) ->
                  'nt1 FStar_TypeChecker_NBETerm.embedding ->
                    'nt2 FStar_TypeChecker_NBETerm.embedding ->
                      'nr FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____15047  ->
    fun uu____15046  ->
      fun uu____15045  ->
        fun uu____15044  ->
          fun uu____15043  ->
            fun uu____15042  ->
              fun uu____15041  ->
                fun uu____15040  ->
                  fun uu____15039  ->
                    fun uu____15038  ->
                      (fun nunivs  ->
                         fun name  ->
                           fun f  ->
                             fun e1  ->
                               fun e2  ->
                                 fun er  ->
                                   fun nf  ->
                                     let nf = Obj.magic nf  in
                                     fun ne1  ->
                                       fun ne2  ->
                                         fun ner  ->
                                           Obj.magic
                                             (mk name (Prims.of_int (3))
                                                nunivs
                                                (mk_total_interpretation_2 f
                                                   e1 e2 er)
                                                (fun cb  ->
                                                   fun args  ->
                                                     let uu____15031 =
                                                       drop nunivs args  in
                                                     mk_total_nbe_interpretation_2
                                                       cb
                                                       (fun uu____15037  ->
                                                          fun uu____15036  ->
                                                            (Obj.magic nf)
                                                              uu____15037
                                                              uu____15036)
                                                       ne1 ne2 ner
                                                       uu____15031)))
                        uu____15047 uu____15046 uu____15045 uu____15044
                        uu____15043 uu____15042 uu____15041 uu____15040
                        uu____15039 uu____15038
  
let mk_total_step_3 :
  'nr 'nt1 'nt2 'nt3 'r 't1 't2 't3 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 'r) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                'r FStar_Syntax_Embeddings.embedding ->
                  ('nt1 -> 'nt2 -> 'nt3 -> 'nr) ->
                    'nt1 FStar_TypeChecker_NBETerm.embedding ->
                      'nt2 FStar_TypeChecker_NBETerm.embedding ->
                        'nt3 FStar_TypeChecker_NBETerm.embedding ->
                          'nr FStar_TypeChecker_NBETerm.embedding ->
                            FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____15248  ->
    fun uu____15247  ->
      fun uu____15246  ->
        fun uu____15245  ->
          fun uu____15244  ->
            fun uu____15243  ->
              fun uu____15242  ->
                fun uu____15241  ->
                  fun uu____15240  ->
                    fun uu____15239  ->
                      fun uu____15238  ->
                        fun uu____15237  ->
                          (fun nunivs  ->
                             fun name  ->
                               fun f  ->
                                 fun e1  ->
                                   fun e2  ->
                                     fun e3  ->
                                       fun er  ->
                                         fun nf  ->
                                           let nf = Obj.magic nf  in
                                           fun ne1  ->
                                             fun ne2  ->
                                               fun ne3  ->
                                                 fun ner  ->
                                                   Obj.magic
                                                     (mk name
                                                        (Prims.of_int (4))
                                                        nunivs
                                                        (mk_total_interpretation_3
                                                           f e1 e2 e3 er)
                                                        (fun cb  ->
                                                           fun args  ->
                                                             let uu____15229
                                                               =
                                                               drop nunivs
                                                                 args
                                                                in
                                                             mk_total_nbe_interpretation_3
                                                               cb
                                                               (fun
                                                                  uu____15236
                                                                   ->
                                                                  fun
                                                                    uu____15235
                                                                     ->
                                                                    fun
                                                                    uu____15234
                                                                     ->
                                                                    (Obj.magic
                                                                    nf)
                                                                    uu____15236
                                                                    uu____15235
                                                                    uu____15234)
                                                               ne1 ne2 ne3
                                                               ner
                                                               uu____15229)))
                            uu____15248 uu____15247 uu____15246 uu____15245
                            uu____15244 uu____15243 uu____15242 uu____15241
                            uu____15240 uu____15239 uu____15238 uu____15237
  
let mk_total_step_4 :
  'nr 'nt1 'nt2 'nt3 'nt4 'r 't1 't2 't3 't4 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 'r) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  'r FStar_Syntax_Embeddings.embedding ->
                    ('nt1 -> 'nt2 -> 'nt3 -> 'nt4 -> 'nr) ->
                      'nt1 FStar_TypeChecker_NBETerm.embedding ->
                        'nt2 FStar_TypeChecker_NBETerm.embedding ->
                          'nt3 FStar_TypeChecker_NBETerm.embedding ->
                            'nt4 FStar_TypeChecker_NBETerm.embedding ->
                              'nr FStar_TypeChecker_NBETerm.embedding ->
                                FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____15490  ->
    fun uu____15489  ->
      fun uu____15488  ->
        fun uu____15487  ->
          fun uu____15486  ->
            fun uu____15485  ->
              fun uu____15484  ->
                fun uu____15483  ->
                  fun uu____15482  ->
                    fun uu____15481  ->
                      fun uu____15480  ->
                        fun uu____15479  ->
                          fun uu____15478  ->
                            fun uu____15477  ->
                              (fun nunivs  ->
                                 fun name  ->
                                   fun f  ->
                                     fun e1  ->
                                       fun e2  ->
                                         fun e3  ->
                                           fun e4  ->
                                             fun er  ->
                                               fun nf  ->
                                                 let nf = Obj.magic nf  in
                                                 fun ne1  ->
                                                   fun ne2  ->
                                                     fun ne3  ->
                                                       fun ne4  ->
                                                         fun ner  ->
                                                           Obj.magic
                                                             (mk name
                                                                (Prims.of_int (5))
                                                                nunivs
                                                                (mk_total_interpretation_4
                                                                   f e1 e2 e3
                                                                   e4 er)
                                                                (fun cb  ->
                                                                   fun args 
                                                                    ->
                                                                    let uu____15468
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_total_nbe_interpretation_4
                                                                    cb
                                                                    (fun
                                                                    uu____15476
                                                                     ->
                                                                    fun
                                                                    uu____15475
                                                                     ->
                                                                    fun
                                                                    uu____15474
                                                                     ->
                                                                    fun
                                                                    uu____15473
                                                                     ->
                                                                    (Obj.magic
                                                                    nf)
                                                                    uu____15476
                                                                    uu____15475
                                                                    uu____15474
                                                                    uu____15473)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ner
                                                                    uu____15468)))
                                uu____15490 uu____15489 uu____15488
                                uu____15487 uu____15486 uu____15485
                                uu____15484 uu____15483 uu____15482
                                uu____15481 uu____15480 uu____15479
                                uu____15478 uu____15477
  
let mk_total_step_5 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'r 't1 't2 't3 't4 't5 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  't5 FStar_Syntax_Embeddings.embedding ->
                    'r FStar_Syntax_Embeddings.embedding ->
                      ('nt1 -> 'nt2 -> 'nt3 -> 'nt4 -> 'nt5 -> 'nr) ->
                        'nt1 FStar_TypeChecker_NBETerm.embedding ->
                          'nt2 FStar_TypeChecker_NBETerm.embedding ->
                            'nt3 FStar_TypeChecker_NBETerm.embedding ->
                              'nt4 FStar_TypeChecker_NBETerm.embedding ->
                                'nt5 FStar_TypeChecker_NBETerm.embedding ->
                                  'nr FStar_TypeChecker_NBETerm.embedding ->
                                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____15773  ->
    fun uu____15772  ->
      fun uu____15771  ->
        fun uu____15770  ->
          fun uu____15769  ->
            fun uu____15768  ->
              fun uu____15767  ->
                fun uu____15766  ->
                  fun uu____15765  ->
                    fun uu____15764  ->
                      fun uu____15763  ->
                        fun uu____15762  ->
                          fun uu____15761  ->
                            fun uu____15760  ->
                              fun uu____15759  ->
                                fun uu____15758  ->
                                  (fun nunivs  ->
                                     fun name  ->
                                       fun f  ->
                                         fun e1  ->
                                           fun e2  ->
                                             fun e3  ->
                                               fun e4  ->
                                                 fun e5  ->
                                                   fun er  ->
                                                     fun nf  ->
                                                       let nf = Obj.magic nf
                                                          in
                                                       fun ne1  ->
                                                         fun ne2  ->
                                                           fun ne3  ->
                                                             fun ne4  ->
                                                               fun ne5  ->
                                                                 fun ner  ->
                                                                   Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (6))
                                                                    nunivs
                                                                    (mk_total_interpretation_5
                                                                    f e1 e2
                                                                    e3 e4 e5
                                                                    er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____15748
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_total_nbe_interpretation_5
                                                                    cb
                                                                    (fun
                                                                    uu____15757
                                                                     ->
                                                                    fun
                                                                    uu____15756
                                                                     ->
                                                                    fun
                                                                    uu____15755
                                                                     ->
                                                                    fun
                                                                    uu____15754
                                                                     ->
                                                                    fun
                                                                    uu____15753
                                                                     ->
                                                                    (Obj.magic
                                                                    nf)
                                                                    uu____15757
                                                                    uu____15756
                                                                    uu____15755
                                                                    uu____15754
                                                                    uu____15753)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ner
                                                                    uu____15748)))
                                    uu____15773 uu____15772 uu____15771
                                    uu____15770 uu____15769 uu____15768
                                    uu____15767 uu____15766 uu____15765
                                    uu____15764 uu____15763 uu____15762
                                    uu____15761 uu____15760 uu____15759
                                    uu____15758
  
let mk_total_step_6 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'nt6 'r 't1 't2 't3 't4 't5 't6 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  't5 FStar_Syntax_Embeddings.embedding ->
                    't6 FStar_Syntax_Embeddings.embedding ->
                      'r FStar_Syntax_Embeddings.embedding ->
                        ('nt1 -> 'nt2 -> 'nt3 -> 'nt4 -> 'nt5 -> 'nt6 -> 'nr)
                          ->
                          'nt1 FStar_TypeChecker_NBETerm.embedding ->
                            'nt2 FStar_TypeChecker_NBETerm.embedding ->
                              'nt3 FStar_TypeChecker_NBETerm.embedding ->
                                'nt4 FStar_TypeChecker_NBETerm.embedding ->
                                  'nt5 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt6 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nr FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____16097  ->
    fun uu____16096  ->
      fun uu____16095  ->
        fun uu____16094  ->
          fun uu____16093  ->
            fun uu____16092  ->
              fun uu____16091  ->
                fun uu____16090  ->
                  fun uu____16089  ->
                    fun uu____16088  ->
                      fun uu____16087  ->
                        fun uu____16086  ->
                          fun uu____16085  ->
                            fun uu____16084  ->
                              fun uu____16083  ->
                                fun uu____16082  ->
                                  fun uu____16081  ->
                                    fun uu____16080  ->
                                      (fun nunivs  ->
                                         fun name  ->
                                           fun f  ->
                                             fun e1  ->
                                               fun e2  ->
                                                 fun e3  ->
                                                   fun e4  ->
                                                     fun e5  ->
                                                       fun e6  ->
                                                         fun er  ->
                                                           fun nf  ->
                                                             let nf =
                                                               Obj.magic nf
                                                                in
                                                             fun ne1  ->
                                                               fun ne2  ->
                                                                 fun ne3  ->
                                                                   fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (7))
                                                                    nunivs
                                                                    (mk_total_interpretation_6
                                                                    f e1 e2
                                                                    e3 e4 e5
                                                                    e6 er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____16069
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_total_nbe_interpretation_6
                                                                    cb
                                                                    (fun
                                                                    uu____16079
                                                                     ->
                                                                    fun
                                                                    uu____16078
                                                                     ->
                                                                    fun
                                                                    uu____16077
                                                                     ->
                                                                    fun
                                                                    uu____16076
                                                                     ->
                                                                    fun
                                                                    uu____16075
                                                                     ->
                                                                    fun
                                                                    uu____16074
                                                                     ->
                                                                    (Obj.magic
                                                                    nf)
                                                                    uu____16079
                                                                    uu____16078
                                                                    uu____16077
                                                                    uu____16076
                                                                    uu____16075
                                                                    uu____16074)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ner
                                                                    uu____16069)))
                                        uu____16097 uu____16096 uu____16095
                                        uu____16094 uu____16093 uu____16092
                                        uu____16091 uu____16090 uu____16089
                                        uu____16088 uu____16087 uu____16086
                                        uu____16085 uu____16084 uu____16083
                                        uu____16082 uu____16081 uu____16080
  
let mk_total_step_7 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'nt6 'nt7 'r 't1 't2 't3 't4 't5 't6 't7 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  't5 FStar_Syntax_Embeddings.embedding ->
                    't6 FStar_Syntax_Embeddings.embedding ->
                      't7 FStar_Syntax_Embeddings.embedding ->
                        'r FStar_Syntax_Embeddings.embedding ->
                          ('nt1 ->
                             'nt2 ->
                               'nt3 -> 'nt4 -> 'nt5 -> 'nt6 -> 'nt7 -> 'nr)
                            ->
                            'nt1 FStar_TypeChecker_NBETerm.embedding ->
                              'nt2 FStar_TypeChecker_NBETerm.embedding ->
                                'nt3 FStar_TypeChecker_NBETerm.embedding ->
                                  'nt4 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt5 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nt6
                                        FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        'nt7
                                          FStar_TypeChecker_NBETerm.embedding
                                          ->
                                          'nr
                                            FStar_TypeChecker_NBETerm.embedding
                                            ->
                                            FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____16462  ->
    fun uu____16461  ->
      fun uu____16460  ->
        fun uu____16459  ->
          fun uu____16458  ->
            fun uu____16457  ->
              fun uu____16456  ->
                fun uu____16455  ->
                  fun uu____16454  ->
                    fun uu____16453  ->
                      fun uu____16452  ->
                        fun uu____16451  ->
                          fun uu____16450  ->
                            fun uu____16449  ->
                              fun uu____16448  ->
                                fun uu____16447  ->
                                  fun uu____16446  ->
                                    fun uu____16445  ->
                                      fun uu____16444  ->
                                        fun uu____16443  ->
                                          (fun nunivs  ->
                                             fun name  ->
                                               fun f  ->
                                                 fun e1  ->
                                                   fun e2  ->
                                                     fun e3  ->
                                                       fun e4  ->
                                                         fun e5  ->
                                                           fun e6  ->
                                                             fun e7  ->
                                                               fun er  ->
                                                                 fun nf  ->
                                                                   let nf =
                                                                    Obj.magic
                                                                    nf  in
                                                                   fun ne1 
                                                                    ->
                                                                    fun ne2 
                                                                    ->
                                                                    fun ne3 
                                                                    ->
                                                                    fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ne7 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (8))
                                                                    nunivs
                                                                    (mk_total_interpretation_7
                                                                    f e1 e2
                                                                    e3 e4 e5
                                                                    e6 e7 er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____16431
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_total_nbe_interpretation_7
                                                                    cb
                                                                    (fun
                                                                    uu____16442
                                                                     ->
                                                                    fun
                                                                    uu____16441
                                                                     ->
                                                                    fun
                                                                    uu____16440
                                                                     ->
                                                                    fun
                                                                    uu____16439
                                                                     ->
                                                                    fun
                                                                    uu____16438
                                                                     ->
                                                                    fun
                                                                    uu____16437
                                                                     ->
                                                                    fun
                                                                    uu____16436
                                                                     ->
                                                                    (Obj.magic
                                                                    nf)
                                                                    uu____16442
                                                                    uu____16441
                                                                    uu____16440
                                                                    uu____16439
                                                                    uu____16438
                                                                    uu____16437
                                                                    uu____16436)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ne7 ner
                                                                    uu____16431)))
                                            uu____16462 uu____16461
                                            uu____16460 uu____16459
                                            uu____16458 uu____16457
                                            uu____16456 uu____16455
                                            uu____16454 uu____16453
                                            uu____16452 uu____16451
                                            uu____16450 uu____16449
                                            uu____16448 uu____16447
                                            uu____16446 uu____16445
                                            uu____16444 uu____16443
  
let mk_total_step_8 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'nt6 'nt7 'nt8 'r 't1 't2 't3 't4 't5 't6 't7
    't8 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r) ->
          't1 FStar_Syntax_Embeddings.embedding ->
            't2 FStar_Syntax_Embeddings.embedding ->
              't3 FStar_Syntax_Embeddings.embedding ->
                't4 FStar_Syntax_Embeddings.embedding ->
                  't5 FStar_Syntax_Embeddings.embedding ->
                    't6 FStar_Syntax_Embeddings.embedding ->
                      't7 FStar_Syntax_Embeddings.embedding ->
                        't8 FStar_Syntax_Embeddings.embedding ->
                          'r FStar_Syntax_Embeddings.embedding ->
                            ('nt1 ->
                               'nt2 ->
                                 'nt3 ->
                                   'nt4 ->
                                     'nt5 -> 'nt6 -> 'nt7 -> 'nt8 -> 'nr)
                              ->
                              'nt1 FStar_TypeChecker_NBETerm.embedding ->
                                'nt2 FStar_TypeChecker_NBETerm.embedding ->
                                  'nt3 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt4 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nt5
                                        FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        'nt6
                                          FStar_TypeChecker_NBETerm.embedding
                                          ->
                                          'nt7
                                            FStar_TypeChecker_NBETerm.embedding
                                            ->
                                            'nt8
                                              FStar_TypeChecker_NBETerm.embedding
                                              ->
                                              'nr
                                                FStar_TypeChecker_NBETerm.embedding
                                                ->
                                                FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____16868  ->
    fun uu____16867  ->
      fun uu____16866  ->
        fun uu____16865  ->
          fun uu____16864  ->
            fun uu____16863  ->
              fun uu____16862  ->
                fun uu____16861  ->
                  fun uu____16860  ->
                    fun uu____16859  ->
                      fun uu____16858  ->
                        fun uu____16857  ->
                          fun uu____16856  ->
                            fun uu____16855  ->
                              fun uu____16854  ->
                                fun uu____16853  ->
                                  fun uu____16852  ->
                                    fun uu____16851  ->
                                      fun uu____16850  ->
                                        fun uu____16849  ->
                                          fun uu____16848  ->
                                            fun uu____16847  ->
                                              (fun nunivs  ->
                                                 fun name  ->
                                                   fun f  ->
                                                     fun e1  ->
                                                       fun e2  ->
                                                         fun e3  ->
                                                           fun e4  ->
                                                             fun e5  ->
                                                               fun e6  ->
                                                                 fun e7  ->
                                                                   fun e8  ->
                                                                    fun er 
                                                                    ->
                                                                    fun nf 
                                                                    ->
                                                                    let nf =
                                                                    Obj.magic
                                                                    nf  in
                                                                    fun ne1 
                                                                    ->
                                                                    fun ne2 
                                                                    ->
                                                                    fun ne3 
                                                                    ->
                                                                    fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ne7 
                                                                    ->
                                                                    fun ne8 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (9))
                                                                    nunivs
                                                                    (mk_total_interpretation_8
                                                                    f e1 e2
                                                                    e3 e4 e5
                                                                    e6 e7 e8
                                                                    er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____16834
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_total_nbe_interpretation_8
                                                                    cb
                                                                    (fun
                                                                    uu____16846
                                                                     ->
                                                                    fun
                                                                    uu____16845
                                                                     ->
                                                                    fun
                                                                    uu____16844
                                                                     ->
                                                                    fun
                                                                    uu____16843
                                                                     ->
                                                                    fun
                                                                    uu____16842
                                                                     ->
                                                                    fun
                                                                    uu____16841
                                                                     ->
                                                                    fun
                                                                    uu____16840
                                                                     ->
                                                                    fun
                                                                    uu____16839
                                                                     ->
                                                                    (Obj.magic
                                                                    nf)
                                                                    uu____16846
                                                                    uu____16845
                                                                    uu____16844
                                                                    uu____16843
                                                                    uu____16842
                                                                    uu____16841
                                                                    uu____16840
                                                                    uu____16839)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ne7 ne8
                                                                    ner
                                                                    uu____16834)))
                                                uu____16868 uu____16867
                                                uu____16866 uu____16865
                                                uu____16864 uu____16863
                                                uu____16862 uu____16861
                                                uu____16860 uu____16859
                                                uu____16858 uu____16857
                                                uu____16856 uu____16855
                                                uu____16854 uu____16853
                                                uu____16852 uu____16851
                                                uu____16850 uu____16849
                                                uu____16848 uu____16847
  
let mk_total_step_9 :
  'nr 'nt1 'nt2 'nt3 'nt4 'nt5 'nt6 'nt7 'nt8 'nt9 'r 't1 't2 't3 't4 't5 't6
    't7 't8 't9 .
    Prims.int ->
      Prims.string ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r)
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
                            'r FStar_Syntax_Embeddings.embedding ->
                              ('nt1 ->
                                 'nt2 ->
                                   'nt3 ->
                                     'nt4 ->
                                       'nt5 ->
                                         'nt6 -> 'nt7 -> 'nt8 -> 'nt9 -> 'nr)
                                ->
                                'nt1 FStar_TypeChecker_NBETerm.embedding ->
                                  'nt2 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt3 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nt4
                                        FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        'nt5
                                          FStar_TypeChecker_NBETerm.embedding
                                          ->
                                          'nt6
                                            FStar_TypeChecker_NBETerm.embedding
                                            ->
                                            'nt7
                                              FStar_TypeChecker_NBETerm.embedding
                                              ->
                                              'nt8
                                                FStar_TypeChecker_NBETerm.embedding
                                                ->
                                                'nt9
                                                  FStar_TypeChecker_NBETerm.embedding
                                                  ->
                                                  'nr
                                                    FStar_TypeChecker_NBETerm.embedding
                                                    ->
                                                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____17315  ->
    fun uu____17314  ->
      fun uu____17313  ->
        fun uu____17312  ->
          fun uu____17311  ->
            fun uu____17310  ->
              fun uu____17309  ->
                fun uu____17308  ->
                  fun uu____17307  ->
                    fun uu____17306  ->
                      fun uu____17305  ->
                        fun uu____17304  ->
                          fun uu____17303  ->
                            fun uu____17302  ->
                              fun uu____17301  ->
                                fun uu____17300  ->
                                  fun uu____17299  ->
                                    fun uu____17298  ->
                                      fun uu____17297  ->
                                        fun uu____17296  ->
                                          fun uu____17295  ->
                                            fun uu____17294  ->
                                              fun uu____17293  ->
                                                fun uu____17292  ->
                                                  (fun nunivs  ->
                                                     fun name  ->
                                                       fun f  ->
                                                         fun e1  ->
                                                           fun e2  ->
                                                             fun e3  ->
                                                               fun e4  ->
                                                                 fun e5  ->
                                                                   fun e6  ->
                                                                    fun e7 
                                                                    ->
                                                                    fun e8 
                                                                    ->
                                                                    fun e9 
                                                                    ->
                                                                    fun er 
                                                                    ->
                                                                    fun nf 
                                                                    ->
                                                                    let nf =
                                                                    Obj.magic
                                                                    nf  in
                                                                    fun ne1 
                                                                    ->
                                                                    fun ne2 
                                                                    ->
                                                                    fun ne3 
                                                                    ->
                                                                    fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ne7 
                                                                    ->
                                                                    fun ne8 
                                                                    ->
                                                                    fun ne9 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (10))
                                                                    nunivs
                                                                    (mk_total_interpretation_9
                                                                    f e1 e2
                                                                    e3 e4 e5
                                                                    e6 e7 e8
                                                                    e9 er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____17278
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_total_nbe_interpretation_9
                                                                    cb
                                                                    (fun
                                                                    uu____17291
                                                                     ->
                                                                    fun
                                                                    uu____17290
                                                                     ->
                                                                    fun
                                                                    uu____17289
                                                                     ->
                                                                    fun
                                                                    uu____17288
                                                                     ->
                                                                    fun
                                                                    uu____17287
                                                                     ->
                                                                    fun
                                                                    uu____17286
                                                                     ->
                                                                    fun
                                                                    uu____17285
                                                                     ->
                                                                    fun
                                                                    uu____17284
                                                                     ->
                                                                    fun
                                                                    uu____17283
                                                                     ->
                                                                    (Obj.magic
                                                                    nf)
                                                                    uu____17291
                                                                    uu____17290
                                                                    uu____17289
                                                                    uu____17288
                                                                    uu____17287
                                                                    uu____17286
                                                                    uu____17285
                                                                    uu____17284
                                                                    uu____17283)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ne7 ne8
                                                                    ne9 ner
                                                                    uu____17278)))
                                                    uu____17315 uu____17314
                                                    uu____17313 uu____17312
                                                    uu____17311 uu____17310
                                                    uu____17309 uu____17308
                                                    uu____17307 uu____17306
                                                    uu____17305 uu____17304
                                                    uu____17303 uu____17302
                                                    uu____17301 uu____17300
                                                    uu____17299 uu____17298
                                                    uu____17297 uu____17296
                                                    uu____17295 uu____17294
                                                    uu____17293 uu____17292
  
let mk_total_step_10 :
  'nr 'nt1 'nt10 'nt2 'nt3 'nt4 'nt5 'nt6 'nt7 'nt8 'nt9 'r 't1 't10 't2 't3
    't4 't5 't6 't7 't8 't9 .
    Prims.int ->
      Prims.string ->
        ('t1 ->
           't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r)
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
                              'r FStar_Syntax_Embeddings.embedding ->
                                ('nt1 ->
                                   'nt2 ->
                                     'nt3 ->
                                       'nt4 ->
                                         'nt5 ->
                                           'nt6 ->
                                             'nt7 ->
                                               'nt8 -> 'nt9 -> 'nt10 -> 'nr)
                                  ->
                                  'nt1 FStar_TypeChecker_NBETerm.embedding ->
                                    'nt2 FStar_TypeChecker_NBETerm.embedding
                                      ->
                                      'nt3
                                        FStar_TypeChecker_NBETerm.embedding
                                        ->
                                        'nt4
                                          FStar_TypeChecker_NBETerm.embedding
                                          ->
                                          'nt5
                                            FStar_TypeChecker_NBETerm.embedding
                                            ->
                                            'nt6
                                              FStar_TypeChecker_NBETerm.embedding
                                              ->
                                              'nt7
                                                FStar_TypeChecker_NBETerm.embedding
                                                ->
                                                'nt8
                                                  FStar_TypeChecker_NBETerm.embedding
                                                  ->
                                                  'nt9
                                                    FStar_TypeChecker_NBETerm.embedding
                                                    ->
                                                    'nt10
                                                      FStar_TypeChecker_NBETerm.embedding
                                                      ->
                                                      'nr
                                                        FStar_TypeChecker_NBETerm.embedding
                                                        ->
                                                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uu____17803  ->
    fun uu____17802  ->
      fun uu____17801  ->
        fun uu____17800  ->
          fun uu____17799  ->
            fun uu____17798  ->
              fun uu____17797  ->
                fun uu____17796  ->
                  fun uu____17795  ->
                    fun uu____17794  ->
                      fun uu____17793  ->
                        fun uu____17792  ->
                          fun uu____17791  ->
                            fun uu____17790  ->
                              fun uu____17789  ->
                                fun uu____17788  ->
                                  fun uu____17787  ->
                                    fun uu____17786  ->
                                      fun uu____17785  ->
                                        fun uu____17784  ->
                                          fun uu____17783  ->
                                            fun uu____17782  ->
                                              fun uu____17781  ->
                                                fun uu____17780  ->
                                                  fun uu____17779  ->
                                                    fun uu____17778  ->
                                                      (fun nunivs  ->
                                                         fun name  ->
                                                           fun f  ->
                                                             fun e1  ->
                                                               fun e2  ->
                                                                 fun e3  ->
                                                                   fun e4  ->
                                                                    fun e5 
                                                                    ->
                                                                    fun e6 
                                                                    ->
                                                                    fun e7 
                                                                    ->
                                                                    fun e8 
                                                                    ->
                                                                    fun e9 
                                                                    ->
                                                                    fun e10 
                                                                    ->
                                                                    fun er 
                                                                    ->
                                                                    fun nf 
                                                                    ->
                                                                    let nf =
                                                                    Obj.magic
                                                                    nf  in
                                                                    fun ne1 
                                                                    ->
                                                                    fun ne2 
                                                                    ->
                                                                    fun ne3 
                                                                    ->
                                                                    fun ne4 
                                                                    ->
                                                                    fun ne5 
                                                                    ->
                                                                    fun ne6 
                                                                    ->
                                                                    fun ne7 
                                                                    ->
                                                                    fun ne8 
                                                                    ->
                                                                    fun ne9 
                                                                    ->
                                                                    fun ne10 
                                                                    ->
                                                                    fun ner 
                                                                    ->
                                                                    Obj.magic
                                                                    (mk name
                                                                    (Prims.of_int (11))
                                                                    nunivs
                                                                    (mk_total_interpretation_10
                                                                    f e1 e2
                                                                    e3 e4 e5
                                                                    e6 e7 e8
                                                                    e9 e10 er)
                                                                    (fun cb 
                                                                    ->
                                                                    fun args 
                                                                    ->
                                                                    let uu____17763
                                                                    =
                                                                    drop
                                                                    nunivs
                                                                    args  in
                                                                    mk_total_nbe_interpretation_10
                                                                    cb
                                                                    (fun
                                                                    uu____17777
                                                                     ->
                                                                    fun
                                                                    uu____17776
                                                                     ->
                                                                    fun
                                                                    uu____17775
                                                                     ->
                                                                    fun
                                                                    uu____17774
                                                                     ->
                                                                    fun
                                                                    uu____17773
                                                                     ->
                                                                    fun
                                                                    uu____17772
                                                                     ->
                                                                    fun
                                                                    uu____17771
                                                                     ->
                                                                    fun
                                                                    uu____17770
                                                                     ->
                                                                    fun
                                                                    uu____17769
                                                                     ->
                                                                    fun
                                                                    uu____17768
                                                                     ->
                                                                    (Obj.magic
                                                                    nf)
                                                                    uu____17777
                                                                    uu____17776
                                                                    uu____17775
                                                                    uu____17774
                                                                    uu____17773
                                                                    uu____17772
                                                                    uu____17771
                                                                    uu____17770
                                                                    uu____17769
                                                                    uu____17768)
                                                                    ne1 ne2
                                                                    ne3 ne4
                                                                    ne5 ne6
                                                                    ne7 ne8
                                                                    ne9 ne10
                                                                    ner
                                                                    uu____17763)))
                                                        uu____17803
                                                        uu____17802
                                                        uu____17801
                                                        uu____17800
                                                        uu____17799
                                                        uu____17798
                                                        uu____17797
                                                        uu____17796
                                                        uu____17795
                                                        uu____17794
                                                        uu____17793
                                                        uu____17792
                                                        uu____17791
                                                        uu____17790
                                                        uu____17789
                                                        uu____17788
                                                        uu____17787
                                                        uu____17786
                                                        uu____17785
                                                        uu____17784
                                                        uu____17783
                                                        uu____17782
                                                        uu____17781
                                                        uu____17780
                                                        uu____17779
                                                        uu____17778
  