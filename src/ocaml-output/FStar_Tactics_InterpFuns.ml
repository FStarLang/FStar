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
  fun nunivs  ->
    fun name  ->
      fun t  ->
        fun e1  ->
          fun e2  ->
            fun er  ->
              fun nt  ->
                fun ne1  ->
                  fun ne2  ->
                    fun ner  ->
                      mk name (Prims.of_int (3)) nunivs
                        (mk_tactic_interpretation_2 t e1 e2 er)
                        (fun cb  ->
                           fun args  ->
                             let uu____11941 = drop nunivs args  in
                             mk_tactic_nbe_interpretation_2 cb nt ne1 ne2 ner
                               uu____11941)
  
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
  fun nunivs  ->
    fun name  ->
      fun t  ->
        fun e1  ->
          fun e2  ->
            fun e3  ->
              fun er  ->
                fun nt  ->
                  fun ne1  ->
                    fun ne2  ->
                      fun ne3  ->
                        fun ner  ->
                          mk name (Prims.of_int (4)) nunivs
                            (mk_tactic_interpretation_3 t e1 e2 e3 er)
                            (fun cb  ->
                               fun args  ->
                                 let uu____12135 = drop nunivs args  in
                                 mk_tactic_nbe_interpretation_3 cb nt ne1 ne2
                                   ne3 ner uu____12135)
  
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
  fun nunivs  ->
    fun name  ->
      fun t  ->
        fun e1  ->
          fun e2  ->
            fun e3  ->
              fun e4  ->
                fun er  ->
                  fun nt  ->
                    fun ne1  ->
                      fun ne2  ->
                        fun ne3  ->
                          fun ne4  ->
                            fun ner  ->
                              mk name (Prims.of_int (5)) nunivs
                                (mk_tactic_interpretation_4 t e1 e2 e3 e4 er)
                                (fun cb  ->
                                   fun args  ->
                                     let uu____12367 = drop nunivs args  in
                                     mk_tactic_nbe_interpretation_4 cb nt ne1
                                       ne2 ne3 ne4 ner uu____12367)
  
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
  fun nunivs  ->
    fun name  ->
      fun t  ->
        fun e1  ->
          fun e2  ->
            fun e3  ->
              fun e4  ->
                fun e5  ->
                  fun er  ->
                    fun nt  ->
                      fun ne1  ->
                        fun ne2  ->
                          fun ne3  ->
                            fun ne4  ->
                              fun ne5  ->
                                fun ner  ->
                                  mk name (Prims.of_int (6)) nunivs
                                    (mk_tactic_interpretation_5 t e1 e2 e3 e4
                                       e5 er)
                                    (fun cb  ->
                                       fun args  ->
                                         let uu____12637 = drop nunivs args
                                            in
                                         mk_tactic_nbe_interpretation_5 cb nt
                                           ne1 ne2 ne3 ne4 ne5 ner
                                           uu____12637)
  
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
  fun nunivs  ->
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
                        fun ne1  ->
                          fun ne2  ->
                            fun ne3  ->
                              fun ne4  ->
                                fun ne5  ->
                                  fun ne6  ->
                                    fun ner  ->
                                      mk name (Prims.of_int (7)) nunivs
                                        (mk_tactic_interpretation_6 t e1 e2
                                           e3 e4 e5 e6 er)
                                        (fun cb  ->
                                           fun args  ->
                                             let uu____12945 =
                                               drop nunivs args  in
                                             mk_tactic_nbe_interpretation_6
                                               cb nt ne1 ne2 ne3 ne4 ne5 ne6
                                               ner uu____12945)
  
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
  fun nunivs  ->
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
                          fun ne1  ->
                            fun ne2  ->
                              fun ne3  ->
                                fun ne4  ->
                                  fun ne5  ->
                                    fun ne6  ->
                                      fun ne7  ->
                                        fun ner  ->
                                          mk name (Prims.of_int (8)) nunivs
                                            (mk_tactic_interpretation_7 t e1
                                               e2 e3 e4 e5 e6 e7 er)
                                            (fun cb  ->
                                               fun args  ->
                                                 let uu____13291 =
                                                   drop nunivs args  in
                                                 mk_tactic_nbe_interpretation_7
                                                   cb nt ne1 ne2 ne3 ne4 ne5
                                                   ne6 ne7 ner uu____13291)
  
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
  fun nunivs  ->
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
                        fun er  ->
                          fun nt  ->
                            fun ne1  ->
                              fun ne2  ->
                                fun ne3  ->
                                  fun ne4  ->
                                    fun ne5  ->
                                      fun ne6  ->
                                        fun ne7  ->
                                          fun ne8  ->
                                            fun ner  ->
                                              mk name (Prims.of_int (9))
                                                nunivs
                                                (mk_tactic_interpretation_8 t
                                                   e1 e2 e3 e4 e5 e6 e7 e8 er)
                                                (fun cb  ->
                                                   fun args  ->
                                                     let uu____13675 =
                                                       drop nunivs args  in
                                                     mk_tactic_nbe_interpretation_8
                                                       cb nt ne1 ne2 ne3 ne4
                                                       ne5 ne6 ne7 ne8 ner
                                                       uu____13675)
  
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
  fun nunivs  ->
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
                        fun e9  ->
                          fun er  ->
                            fun nt  ->
                              fun ne1  ->
                                fun ne2  ->
                                  fun ne3  ->
                                    fun ne4  ->
                                      fun ne5  ->
                                        fun ne6  ->
                                          fun ne7  ->
                                            fun ne8  ->
                                              fun ne9  ->
                                                fun ner  ->
                                                  mk name (Prims.of_int (10))
                                                    nunivs
                                                    (mk_tactic_interpretation_9
                                                       t e1 e2 e3 e4 e5 e6 e7
                                                       e8 e9 er)
                                                    (fun cb  ->
                                                       fun args  ->
                                                         let uu____14097 =
                                                           drop nunivs args
                                                            in
                                                         mk_tactic_nbe_interpretation_9
                                                           cb nt ne1 ne2 ne3
                                                           ne4 ne5 ne6 ne7
                                                           ne8 ne9 ner
                                                           uu____14097)
  
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
  fun nunivs  ->
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
                        fun e9  ->
                          fun e10  ->
                            fun er  ->
                              fun nt  ->
                                fun ne1  ->
                                  fun ne2  ->
                                    fun ne3  ->
                                      fun ne4  ->
                                        fun ne5  ->
                                          fun ne6  ->
                                            fun ne7  ->
                                              fun ne8  ->
                                                fun ne9  ->
                                                  fun ne10  ->
                                                    fun ner  ->
                                                      mk name
                                                        (Prims.of_int (11))
                                                        nunivs
                                                        (mk_tactic_interpretation_10
                                                           t e1 e2 e3 e4 e5
                                                           e6 e7 e8 e9 e10 er)
                                                        (fun cb  ->
                                                           fun args  ->
                                                             let uu____14557
                                                               =
                                                               drop nunivs
                                                                 args
                                                                in
                                                             mk_tactic_nbe_interpretation_10
                                                               cb nt ne1 ne2
                                                               ne3 ne4 ne5
                                                               ne6 ne7 ne8
                                                               ne9 ne10 ner
                                                               uu____14557)
  
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
                         let uu____14667 = drop nunivs args  in
                         mk_total_nbe_interpretation_1 cb nf ne1 ner
                           uu____14667)
  
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
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun e1  ->
          fun e2  ->
            fun er  ->
              fun nf  ->
                fun ne1  ->
                  fun ne2  ->
                    fun ner  ->
                      mk name (Prims.of_int (3)) nunivs
                        (mk_total_interpretation_2 f e1 e2 er)
                        (fun cb  ->
                           fun args  ->
                             let uu____14815 = drop nunivs args  in
                             mk_total_nbe_interpretation_2 cb nf ne1 ne2 ner
                               uu____14815)
  
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
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun e1  ->
          fun e2  ->
            fun e3  ->
              fun er  ->
                fun nf  ->
                  fun ne1  ->
                    fun ne2  ->
                      fun ne3  ->
                        fun ner  ->
                          mk name (Prims.of_int (4)) nunivs
                            (mk_total_interpretation_3 f e1 e2 e3 er)
                            (fun cb  ->
                               fun args  ->
                                 let uu____15001 = drop nunivs args  in
                                 mk_total_nbe_interpretation_3 cb nf ne1 ne2
                                   ne3 ner uu____15001)
  
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
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun e1  ->
          fun e2  ->
            fun e3  ->
              fun e4  ->
                fun er  ->
                  fun nf  ->
                    fun ne1  ->
                      fun ne2  ->
                        fun ne3  ->
                          fun ne4  ->
                            fun ner  ->
                              mk name (Prims.of_int (5)) nunivs
                                (mk_total_interpretation_4 f e1 e2 e3 e4 er)
                                (fun cb  ->
                                   fun args  ->
                                     let uu____15225 = drop nunivs args  in
                                     mk_total_nbe_interpretation_4 cb nf ne1
                                       ne2 ne3 ne4 ner uu____15225)
  
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
  fun nunivs  ->
    fun name  ->
      fun f  ->
        fun e1  ->
          fun e2  ->
            fun e3  ->
              fun e4  ->
                fun e5  ->
                  fun er  ->
                    fun nf  ->
                      fun ne1  ->
                        fun ne2  ->
                          fun ne3  ->
                            fun ne4  ->
                              fun ne5  ->
                                fun ner  ->
                                  mk name (Prims.of_int (6)) nunivs
                                    (mk_total_interpretation_5 f e1 e2 e3 e4
                                       e5 er)
                                    (fun cb  ->
                                       fun args  ->
                                         let uu____15487 = drop nunivs args
                                            in
                                         mk_total_nbe_interpretation_5 cb nf
                                           ne1 ne2 ne3 ne4 ne5 ner
                                           uu____15487)
  
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
  fun nunivs  ->
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
                        fun ne1  ->
                          fun ne2  ->
                            fun ne3  ->
                              fun ne4  ->
                                fun ne5  ->
                                  fun ne6  ->
                                    fun ner  ->
                                      mk name (Prims.of_int (7)) nunivs
                                        (mk_total_interpretation_6 f e1 e2 e3
                                           e4 e5 e6 er)
                                        (fun cb  ->
                                           fun args  ->
                                             let uu____15787 =
                                               drop nunivs args  in
                                             mk_total_nbe_interpretation_6 cb
                                               nf ne1 ne2 ne3 ne4 ne5 ne6 ner
                                               uu____15787)
  
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
  fun nunivs  ->
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
                          fun ne1  ->
                            fun ne2  ->
                              fun ne3  ->
                                fun ne4  ->
                                  fun ne5  ->
                                    fun ne6  ->
                                      fun ne7  ->
                                        fun ner  ->
                                          mk name (Prims.of_int (8)) nunivs
                                            (mk_total_interpretation_7 f e1
                                               e2 e3 e4 e5 e6 e7 er)
                                            (fun cb  ->
                                               fun args  ->
                                                 let uu____16125 =
                                                   drop nunivs args  in
                                                 mk_total_nbe_interpretation_7
                                                   cb nf ne1 ne2 ne3 ne4 ne5
                                                   ne6 ne7 ner uu____16125)
  
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
  fun nunivs  ->
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
                        fun er  ->
                          fun nf  ->
                            fun ne1  ->
                              fun ne2  ->
                                fun ne3  ->
                                  fun ne4  ->
                                    fun ne5  ->
                                      fun ne6  ->
                                        fun ne7  ->
                                          fun ne8  ->
                                            fun ner  ->
                                              mk name (Prims.of_int (9))
                                                nunivs
                                                (mk_total_interpretation_8 f
                                                   e1 e2 e3 e4 e5 e6 e7 e8 er)
                                                (fun cb  ->
                                                   fun args  ->
                                                     let uu____16501 =
                                                       drop nunivs args  in
                                                     mk_total_nbe_interpretation_8
                                                       cb nf ne1 ne2 ne3 ne4
                                                       ne5 ne6 ne7 ne8 ner
                                                       uu____16501)
  
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
  fun nunivs  ->
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
                        fun e9  ->
                          fun er  ->
                            fun nf  ->
                              fun ne1  ->
                                fun ne2  ->
                                  fun ne3  ->
                                    fun ne4  ->
                                      fun ne5  ->
                                        fun ne6  ->
                                          fun ne7  ->
                                            fun ne8  ->
                                              fun ne9  ->
                                                fun ner  ->
                                                  mk name (Prims.of_int (10))
                                                    nunivs
                                                    (mk_total_interpretation_9
                                                       f e1 e2 e3 e4 e5 e6 e7
                                                       e8 e9 er)
                                                    (fun cb  ->
                                                       fun args  ->
                                                         let uu____16915 =
                                                           drop nunivs args
                                                            in
                                                         mk_total_nbe_interpretation_9
                                                           cb nf ne1 ne2 ne3
                                                           ne4 ne5 ne6 ne7
                                                           ne8 ne9 ner
                                                           uu____16915)
  
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
  fun nunivs  ->
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
                        fun e9  ->
                          fun e10  ->
                            fun er  ->
                              fun nf  ->
                                fun ne1  ->
                                  fun ne2  ->
                                    fun ne3  ->
                                      fun ne4  ->
                                        fun ne5  ->
                                          fun ne6  ->
                                            fun ne7  ->
                                              fun ne8  ->
                                                fun ne9  ->
                                                  fun ne10  ->
                                                    fun ner  ->
                                                      mk name
                                                        (Prims.of_int (11))
                                                        nunivs
                                                        (mk_total_interpretation_10
                                                           f e1 e2 e3 e4 e5
                                                           e6 e7 e8 e9 e10 er)
                                                        (fun cb  ->
                                                           fun args  ->
                                                             let uu____17367
                                                               =
                                                               drop nunivs
                                                                 args
                                                                in
                                                             mk_total_nbe_interpretation_10
                                                               cb nf ne1 ne2
                                                               ne3 ne4 ne5
                                                               ne6 ne7 ne8
                                                               ne9 ne10 ner
                                                               uu____17367)
  