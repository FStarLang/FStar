open Prims
let (norm_before_encoding :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.Eager_unfolding true;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.AllowUnboundUniverses;
        FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]  in
      FStar_TypeChecker_Normalize.normalize steps
        env.FStar_SMTEncoding_Env.tcenv t
  
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term * Prims.int *
          FStar_SMTEncoding_Term.decl Prims.list)
    ;
  is: FStar_Ident.lident -> Prims.bool }
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term * Prims.int *
          FStar_SMTEncoding_Term.decl Prims.list))
  = fun projectee  -> match projectee with | { mk = mk1; is;_} -> mk1 
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  -> match projectee with | { mk = mk1; is;_} -> is 
let (prims : prims_t) =
  let module_name = "Prims"  in
  let uu____280 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____280 with
  | (asym,a) ->
      let uu____304 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____304 with
       | (xsym,x) ->
           let uu____328 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____328 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____431 =
                      let uu____443 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____443, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____431  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____469 =
                      let uu____480 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____480)  in
                    FStar_SMTEncoding_Util.mkApp uu____469  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____526 =
                    let uu____529 =
                      let uu____532 =
                        let uu____535 =
                          let uu____536 =
                            let uu____547 =
                              let uu____554 =
                                let uu____571 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____571)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____554
                               in
                            (uu____547, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____536  in
                        let uu____616 =
                          let uu____619 =
                            let uu____620 =
                              let uu____631 =
                                let uu____638 =
                                  let uu____655 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____655)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____638
                                 in
                              (uu____631,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____620  in
                          [uu____619]  in
                        uu____535 :: uu____616  in
                      xtok_decl :: uu____532  in
                    xname_decl :: uu____529  in
                  (xtok1, (FStar_List.length vars), uu____526)  in
                let axy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(asym, FStar_SMTEncoding_Term.Term_sort);
                    (xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)]
                   in
                let xy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)]
                   in
                let qx =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort)]
                   in
                let prims1 =
                  let uu____868 =
                    let uu____896 =
                      let uu____918 =
                        let uu____925 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____925
                         in
                      quant axy uu____918  in
                    (FStar_Parser_Const.op_Eq, uu____896)  in
                  let uu____967 =
                    let uu____997 =
                      let uu____1025 =
                        let uu____1047 =
                          let uu____1054 =
                            let uu____1061 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____1061  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____1054
                           in
                        quant axy uu____1047  in
                      (FStar_Parser_Const.op_notEq, uu____1025)  in
                    let uu____1103 =
                      let uu____1133 =
                        let uu____1161 =
                          let uu____1183 =
                            let uu____1190 =
                              let uu____1197 =
                                let uu____1208 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____1215 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____1208, uu____1215)  in
                              FStar_SMTEncoding_Util.mkAnd uu____1197  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____1190
                             in
                          quant xy uu____1183  in
                        (FStar_Parser_Const.op_And, uu____1161)  in
                      let uu____1257 =
                        let uu____1287 =
                          let uu____1315 =
                            let uu____1337 =
                              let uu____1344 =
                                let uu____1351 =
                                  let uu____1362 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____1369 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____1362, uu____1369)  in
                                FStar_SMTEncoding_Util.mkOr uu____1351  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1344
                               in
                            quant xy uu____1337  in
                          (FStar_Parser_Const.op_Or, uu____1315)  in
                        let uu____1411 =
                          let uu____1441 =
                            let uu____1469 =
                              let uu____1491 =
                                let uu____1498 =
                                  let uu____1505 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____1505  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1498
                                 in
                              quant qx uu____1491  in
                            (FStar_Parser_Const.op_Negation, uu____1469)  in
                          let uu____1541 =
                            let uu____1571 =
                              let uu____1599 =
                                let uu____1621 =
                                  let uu____1628 =
                                    let uu____1635 =
                                      let uu____1646 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1653 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1646, uu____1653)  in
                                    FStar_SMTEncoding_Util.mkLT uu____1635
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1628
                                   in
                                quant xy uu____1621  in
                              (FStar_Parser_Const.op_LT, uu____1599)  in
                            let uu____1695 =
                              let uu____1725 =
                                let uu____1753 =
                                  let uu____1775 =
                                    let uu____1782 =
                                      let uu____1789 =
                                        let uu____1800 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1807 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1800, uu____1807)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1789
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1782
                                     in
                                  quant xy uu____1775  in
                                (FStar_Parser_Const.op_LTE, uu____1753)  in
                              let uu____1849 =
                                let uu____1879 =
                                  let uu____1907 =
                                    let uu____1929 =
                                      let uu____1936 =
                                        let uu____1943 =
                                          let uu____1954 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1961 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1954, uu____1961)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1943
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1936
                                       in
                                    quant xy uu____1929  in
                                  (FStar_Parser_Const.op_GT, uu____1907)  in
                                let uu____2003 =
                                  let uu____2033 =
                                    let uu____2061 =
                                      let uu____2083 =
                                        let uu____2090 =
                                          let uu____2097 =
                                            let uu____2108 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____2115 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____2108, uu____2115)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____2097
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____2090
                                         in
                                      quant xy uu____2083  in
                                    (FStar_Parser_Const.op_GTE, uu____2061)
                                     in
                                  let uu____2157 =
                                    let uu____2187 =
                                      let uu____2215 =
                                        let uu____2237 =
                                          let uu____2244 =
                                            let uu____2251 =
                                              let uu____2262 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____2269 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____2262, uu____2269)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____2251
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____2244
                                           in
                                        quant xy uu____2237  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____2215)
                                       in
                                    let uu____2311 =
                                      let uu____2341 =
                                        let uu____2369 =
                                          let uu____2391 =
                                            let uu____2398 =
                                              let uu____2405 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____2405
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____2398
                                             in
                                          quant qx uu____2391  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____2369)
                                         in
                                      let uu____2441 =
                                        let uu____2471 =
                                          let uu____2499 =
                                            let uu____2521 =
                                              let uu____2528 =
                                                let uu____2535 =
                                                  let uu____2546 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____2553 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____2546, uu____2553)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____2535
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____2528
                                               in
                                            quant xy uu____2521  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____2499)
                                           in
                                        let uu____2595 =
                                          let uu____2625 =
                                            let uu____2653 =
                                              let uu____2675 =
                                                let uu____2682 =
                                                  let uu____2689 =
                                                    let uu____2700 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____2707 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____2700, uu____2707)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____2689
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____2682
                                                 in
                                              quant xy uu____2675  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____2653)
                                             in
                                          let uu____2749 =
                                            let uu____2779 =
                                              let uu____2807 =
                                                let uu____2829 =
                                                  let uu____2836 =
                                                    let uu____2843 =
                                                      let uu____2854 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____2861 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____2854,
                                                        uu____2861)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____2843
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____2836
                                                   in
                                                quant xy uu____2829  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____2807)
                                               in
                                            let uu____2903 =
                                              let uu____2933 =
                                                let uu____2961 =
                                                  let uu____2983 =
                                                    let uu____2990 =
                                                      let uu____2997 =
                                                        let uu____3008 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____3015 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____3008,
                                                          uu____3015)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____2997
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____2990
                                                     in
                                                  quant xy uu____2983  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____2961)
                                                 in
                                              let uu____3057 =
                                                let uu____3087 =
                                                  let uu____3115 =
                                                    let uu____3137 =
                                                      let uu____3144 =
                                                        let uu____3151 =
                                                          let uu____3162 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____3169 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____3162,
                                                            uu____3169)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____3151
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____3144
                                                       in
                                                    quant xy uu____3137  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____3115)
                                                   in
                                                let uu____3211 =
                                                  let uu____3241 =
                                                    let uu____3269 =
                                                      let uu____3291 =
                                                        let uu____3298 =
                                                          let uu____3305 =
                                                            let uu____3316 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____3323 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____3316,
                                                              uu____3323)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____3305
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____3298
                                                         in
                                                      quant xy uu____3291  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____3269)
                                                     in
                                                  let uu____3365 =
                                                    let uu____3395 =
                                                      let uu____3423 =
                                                        let uu____3445 =
                                                          let uu____3452 =
                                                            let uu____3459 =
                                                              let uu____3470
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____3477
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____3470,
                                                                uu____3477)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____3459
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____3452
                                                           in
                                                        quant xy uu____3445
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____3423)
                                                       in
                                                    let uu____3519 =
                                                      let uu____3549 =
                                                        let uu____3577 =
                                                          let uu____3599 =
                                                            let uu____3606 =
                                                              let uu____3613
                                                                =
                                                                let uu____3624
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____3631
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____3624,
                                                                  uu____3631)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____3613
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____3606
                                                             in
                                                          quant xy uu____3599
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____3577)
                                                         in
                                                      let uu____3673 =
                                                        let uu____3703 =
                                                          let uu____3731 =
                                                            let uu____3753 =
                                                              let uu____3760
                                                                =
                                                                let uu____3767
                                                                  =
                                                                  let uu____3778
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____3785
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____3778,
                                                                    uu____3785)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____3767
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____3760
                                                               in
                                                            quant xy
                                                              uu____3753
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____3731)
                                                           in
                                                        let uu____3827 =
                                                          let uu____3857 =
                                                            let uu____3885 =
                                                              let uu____3907
                                                                =
                                                                let uu____3914
                                                                  =
                                                                  let uu____3921
                                                                    =
                                                                    let uu____3932
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____3939
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____3932,
                                                                    uu____3939)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____3921
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____3914
                                                                 in
                                                              quant xy
                                                                uu____3907
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____3885)
                                                             in
                                                          let uu____3981 =
                                                            let uu____4011 =
                                                              let uu____4039
                                                                =
                                                                let uu____4061
                                                                  =
                                                                  let uu____4068
                                                                    =
                                                                    let uu____4075
                                                                    =
                                                                    let uu____4086
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____4093
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____4086,
                                                                    uu____4093)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____4075
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____4068
                                                                   in
                                                                quant xy
                                                                  uu____4061
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____4039)
                                                               in
                                                            let uu____4135 =
                                                              let uu____4165
                                                                =
                                                                let uu____4193
                                                                  =
                                                                  let uu____4215
                                                                    =
                                                                    let uu____4222
                                                                    =
                                                                    let uu____4229
                                                                    =
                                                                    let uu____4240
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____4247
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____4240,
                                                                    uu____4247)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____4229
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____4222
                                                                     in
                                                                  quant xy
                                                                    uu____4215
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____4193)
                                                                 in
                                                              let uu____4289
                                                                =
                                                                let uu____4319
                                                                  =
                                                                  let uu____4347
                                                                    =
                                                                    let uu____4369
                                                                    =
                                                                    let uu____4376
                                                                    =
                                                                    let uu____4383
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____4383
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____4376
                                                                     in
                                                                    quant qx
                                                                    uu____4369
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____4347)
                                                                   in
                                                                [uu____4319]
                                                                 in
                                                              uu____4165 ::
                                                                uu____4289
                                                               in
                                                            uu____4011 ::
                                                              uu____4135
                                                             in
                                                          uu____3857 ::
                                                            uu____3981
                                                           in
                                                        uu____3703 ::
                                                          uu____3827
                                                         in
                                                      uu____3549 ::
                                                        uu____3673
                                                       in
                                                    uu____3395 :: uu____3519
                                                     in
                                                  uu____3241 :: uu____3365
                                                   in
                                                uu____3087 :: uu____3211  in
                                              uu____2933 :: uu____3057  in
                                            uu____2779 :: uu____2903  in
                                          uu____2625 :: uu____2749  in
                                        uu____2471 :: uu____2595  in
                                      uu____2341 :: uu____2441  in
                                    uu____2187 :: uu____2311  in
                                  uu____2033 :: uu____2157  in
                                uu____1879 :: uu____2003  in
                              uu____1725 :: uu____1849  in
                            uu____1571 :: uu____1695  in
                          uu____1441 :: uu____1541  in
                        uu____1287 :: uu____1411  in
                      uu____1133 :: uu____1257  in
                    uu____997 :: uu____1103  in
                  uu____868 :: uu____967  in
                let mk1 l v1 =
                  let uu____5127 =
                    let uu____5142 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____5260  ->
                              match uu____5260 with
                              | (l',uu____5288) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____5142
                      (FStar_Option.map
                         (fun uu____5421  ->
                            match uu____5421 with
                            | (uu____5459,b) ->
                                let uu____5507 = FStar_Ident.range_of_lid l
                                   in
                                b uu____5507 v1))
                     in
                  FStar_All.pipe_right uu____5127 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____5621  ->
                          match uu____5621 with
                          | (l',uu____5649) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_SMTEncoding_Term.term ->
        (Prims.string * FStar_SMTEncoding_Term.sort * Prims.bool) Prims.list
          -> FStar_SMTEncoding_Term.decl)
  =
  fun rng  ->
    fun env  ->
      fun tapp  ->
        fun vars  ->
          let uu____5765 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____5765 with
          | (xxsym,xx) ->
              let uu____5785 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____5785 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____5816 =
                     let uu____5827 =
                       let uu____5834 =
                         let uu____5851 =
                           let uu____5852 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____5862 =
                             let uu____5873 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____5873 :: vars  in
                           uu____5852 :: uu____5862  in
                         let uu____5899 =
                           let uu____5906 =
                             let uu____5917 =
                               let uu____5924 =
                                 let uu____5935 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____5935)  in
                               FStar_SMTEncoding_Util.mkEq uu____5924  in
                             (xx_has_type, uu____5917)  in
                           FStar_SMTEncoding_Util.mkImp uu____5906  in
                         ([[xx_has_type]], uu____5851, uu____5899)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____5834  in
                     let uu____5993 =
                       let uu____5995 =
                         let uu____5997 =
                           let uu____5999 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____5999  in
                         Prims.op_Hat module_name uu____5997  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____5995
                        in
                     (uu____5827, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____5993)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____5816)
  
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx =
    FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy =
    FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mkForall_fuel1 env =
    let uu____6248 =
      let uu____6250 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____6250  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____6248  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____6400 =
      let uu____6401 =
        let uu____6412 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____6412, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6401  in
    let uu____6426 =
      let uu____6429 =
        let uu____6430 =
          let uu____6441 =
            let uu____6448 =
              let uu____6465 =
                let uu____6472 =
                  let uu____6483 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____6483)  in
                FStar_SMTEncoding_Util.mkImp uu____6472  in
              ([[typing_pred]], [xx], uu____6465)  in
            let uu____6544 =
              let uu____6568 = FStar_TypeChecker_Env.get_range env  in
              let uu____6569 = mkForall_fuel1 env  in uu____6569 uu____6568
               in
            uu____6544 uu____6448  in
          (uu____6441, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____6430  in
      [uu____6429]  in
    uu____6400 :: uu____6426  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____6754 =
      let uu____6755 =
        let uu____6766 =
          let uu____6773 = FStar_TypeChecker_Env.get_range env  in
          let uu____6774 =
            let uu____6791 =
              let uu____6799 =
                let uu____6805 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____6805]  in
              [uu____6799]  in
            let uu____6828 =
              let uu____6835 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____6835 tt  in
            (uu____6791, [bb], uu____6828)  in
          FStar_SMTEncoding_Term.mkForall uu____6773 uu____6774  in
        (uu____6766, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6755  in
    let uu____6875 =
      let uu____6878 =
        let uu____6879 =
          let uu____6890 =
            let uu____6897 =
              let uu____6914 =
                let uu____6921 =
                  let uu____6932 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____6932)  in
                FStar_SMTEncoding_Util.mkImp uu____6921  in
              ([[typing_pred]], [xx], uu____6914)  in
            let uu____6989 =
              let uu____7013 = FStar_TypeChecker_Env.get_range env  in
              let uu____7014 = mkForall_fuel1 env  in uu____7014 uu____7013
               in
            uu____6989 uu____6897  in
          (uu____6890, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____6879  in
      [uu____6878]  in
    uu____6754 :: uu____6875  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____7189 =
        let uu____7190 =
          let uu____7196 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____7196, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____7190  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____7189  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____7243 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____7243  in
    let uu____7278 =
      let uu____7279 =
        let uu____7290 =
          let uu____7297 = FStar_TypeChecker_Env.get_range env  in
          let uu____7298 =
            let uu____7315 =
              let uu____7323 =
                let uu____7329 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____7329]  in
              [uu____7323]  in
            let uu____7352 =
              let uu____7359 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____7359 tt  in
            (uu____7315, [bb], uu____7352)  in
          FStar_SMTEncoding_Term.mkForall uu____7297 uu____7298  in
        (uu____7290, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____7279  in
    let uu____7399 =
      let uu____7402 =
        let uu____7403 =
          let uu____7414 =
            let uu____7421 =
              let uu____7438 =
                let uu____7445 =
                  let uu____7456 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____7456)  in
                FStar_SMTEncoding_Util.mkImp uu____7445  in
              ([[typing_pred]], [xx], uu____7438)  in
            let uu____7513 =
              let uu____7537 = FStar_TypeChecker_Env.get_range env  in
              let uu____7538 = mkForall_fuel1 env  in uu____7538 uu____7537
               in
            uu____7513 uu____7421  in
          (uu____7414, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____7403  in
      let uu____7572 =
        let uu____7575 =
          let uu____7576 =
            let uu____7587 =
              let uu____7594 =
                let uu____7611 =
                  let uu____7618 =
                    let uu____7629 =
                      let uu____7636 =
                        let uu____7642 =
                          let uu____7648 =
                            let uu____7654 =
                              let uu____7661 =
                                let uu____7672 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____7679 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____7672, uu____7679)  in
                              FStar_SMTEncoding_Util.mkGT uu____7661  in
                            let uu____7693 =
                              let uu____7699 =
                                let uu____7706 =
                                  let uu____7717 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____7724 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____7717, uu____7724)  in
                                FStar_SMTEncoding_Util.mkGTE uu____7706  in
                              let uu____7738 =
                                let uu____7744 =
                                  let uu____7751 =
                                    let uu____7762 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____7769 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____7762, uu____7769)  in
                                  FStar_SMTEncoding_Util.mkLT uu____7751  in
                                [uu____7744]  in
                              uu____7699 :: uu____7738  in
                            uu____7654 :: uu____7693  in
                          typing_pred_y :: uu____7648  in
                        typing_pred :: uu____7642  in
                      FStar_SMTEncoding_Util.mk_and_l uu____7636  in
                    (uu____7629, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____7618  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____7611)
                 in
              let uu____7862 =
                let uu____7886 = FStar_TypeChecker_Env.get_range env  in
                let uu____7887 = mkForall_fuel1 env  in uu____7887 uu____7886
                 in
              uu____7862 uu____7594  in
            (uu____7587,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____7576  in
        [uu____7575]  in
      uu____7402 :: uu____7572  in
    uu____7278 :: uu____7399  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____8062 =
        let uu____8063 =
          let uu____8069 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____8069, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____8063  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____8062  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv
        ("a", (FStar_SMTEncoding_Term.Sort "Real"))
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv
        ("b", (FStar_SMTEncoding_Term.Sort "Real"))
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____8118 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8118  in
    let uu____8153 =
      let uu____8154 =
        let uu____8165 =
          let uu____8172 = FStar_TypeChecker_Env.get_range env  in
          let uu____8173 =
            let uu____8190 =
              let uu____8198 =
                let uu____8204 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____8204]  in
              [uu____8198]  in
            let uu____8227 =
              let uu____8234 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8234 tt  in
            (uu____8190, [bb], uu____8227)  in
          FStar_SMTEncoding_Term.mkForall uu____8172 uu____8173  in
        (uu____8165, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____8154  in
    let uu____8274 =
      let uu____8277 =
        let uu____8278 =
          let uu____8289 =
            let uu____8296 =
              let uu____8313 =
                let uu____8320 =
                  let uu____8331 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____8331)  in
                FStar_SMTEncoding_Util.mkImp uu____8320  in
              ([[typing_pred]], [xx], uu____8313)  in
            let uu____8388 =
              let uu____8412 = FStar_TypeChecker_Env.get_range env  in
              let uu____8413 = mkForall_fuel1 env  in uu____8413 uu____8412
               in
            uu____8388 uu____8296  in
          (uu____8289, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____8278  in
      let uu____8447 =
        let uu____8450 =
          let uu____8451 =
            let uu____8462 =
              let uu____8469 =
                let uu____8486 =
                  let uu____8493 =
                    let uu____8504 =
                      let uu____8511 =
                        let uu____8517 =
                          let uu____8523 =
                            let uu____8529 =
                              let uu____8536 =
                                let uu____8547 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____8554 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____8547, uu____8554)  in
                              FStar_SMTEncoding_Util.mkGT uu____8536  in
                            let uu____8568 =
                              let uu____8574 =
                                let uu____8581 =
                                  let uu____8592 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____8599 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____8592, uu____8599)  in
                                FStar_SMTEncoding_Util.mkGTE uu____8581  in
                              let uu____8613 =
                                let uu____8619 =
                                  let uu____8626 =
                                    let uu____8637 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____8644 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____8637, uu____8644)  in
                                  FStar_SMTEncoding_Util.mkLT uu____8626  in
                                [uu____8619]  in
                              uu____8574 :: uu____8613  in
                            uu____8529 :: uu____8568  in
                          typing_pred_y :: uu____8523  in
                        typing_pred :: uu____8517  in
                      FStar_SMTEncoding_Util.mk_and_l uu____8511  in
                    (uu____8504, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____8493  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8486)
                 in
              let uu____8737 =
                let uu____8761 = FStar_TypeChecker_Env.get_range env  in
                let uu____8762 = mkForall_fuel1 env  in uu____8762 uu____8761
                 in
              uu____8737 uu____8469  in
            (uu____8462,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____8451  in
        [uu____8450]  in
      uu____8277 :: uu____8447  in
    uu____8153 :: uu____8274  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8947 =
      let uu____8948 =
        let uu____8959 =
          let uu____8966 = FStar_TypeChecker_Env.get_range env  in
          let uu____8967 =
            let uu____8984 =
              let uu____8992 =
                let uu____8998 = FStar_SMTEncoding_Term.boxString b  in
                [uu____8998]  in
              [uu____8992]  in
            let uu____9021 =
              let uu____9028 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____9028 tt  in
            (uu____8984, [bb], uu____9021)  in
          FStar_SMTEncoding_Term.mkForall uu____8966 uu____8967  in
        (uu____8959, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____8948  in
    let uu____9068 =
      let uu____9071 =
        let uu____9072 =
          let uu____9083 =
            let uu____9090 =
              let uu____9107 =
                let uu____9114 =
                  let uu____9125 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____9125)  in
                FStar_SMTEncoding_Util.mkImp uu____9114  in
              ([[typing_pred]], [xx], uu____9107)  in
            let uu____9182 =
              let uu____9206 = FStar_TypeChecker_Env.get_range env  in
              let uu____9207 = mkForall_fuel1 env  in uu____9207 uu____9206
               in
            uu____9182 uu____9090  in
          (uu____9083, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____9072  in
      [uu____9071]  in
    uu____8947 :: uu____9068  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____9395 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____9395]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____9557 =
      let uu____9558 =
        let uu____9569 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____9569, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____9558  in
    [uu____9557]  in
  let mk_and_interp env conj uu____9664 =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9825 =
      let uu____9826 =
        let uu____9837 =
          let uu____9844 = FStar_TypeChecker_Env.get_range env  in
          let uu____9845 =
            let uu____9862 =
              let uu____9869 =
                let uu____9880 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____9880, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9869  in
            ([[l_and_a_b]], [aa; bb], uu____9862)  in
          FStar_SMTEncoding_Term.mkForall uu____9844 uu____9845  in
        (uu____9837, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____9826  in
    [uu____9825]  in
  let mk_or_interp env disj uu____10031 =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____10192 =
      let uu____10193 =
        let uu____10204 =
          let uu____10211 = FStar_TypeChecker_Env.get_range env  in
          let uu____10212 =
            let uu____10229 =
              let uu____10236 =
                let uu____10247 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____10247, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____10236  in
            ([[l_or_a_b]], [aa; bb], uu____10229)  in
          FStar_SMTEncoding_Term.mkForall uu____10211 uu____10212  in
        (uu____10204, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____10193  in
    [uu____10192]  in
  let mk_eq2_interp env eq2 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort)
       in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____10532 =
      let uu____10533 =
        let uu____10544 =
          let uu____10551 = FStar_TypeChecker_Env.get_range env  in
          let uu____10552 =
            let uu____10569 =
              let uu____10576 =
                let uu____10587 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____10587, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____10576  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____10569)  in
          FStar_SMTEncoding_Term.mkForall uu____10551 uu____10552  in
        (uu____10544, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____10533  in
    [uu____10532]  in
  let mk_eq3_interp env eq3 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort)
       in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____10893 =
      let uu____10894 =
        let uu____10905 =
          let uu____10912 = FStar_TypeChecker_Env.get_range env  in
          let uu____10913 =
            let uu____10930 =
              let uu____10937 =
                let uu____10948 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____10948, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____10937  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____10930)  in
          FStar_SMTEncoding_Term.mkForall uu____10912 uu____10913  in
        (uu____10905, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____10894  in
    [uu____10893]  in
  let mk_imp_interp env imp tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____11276 =
      let uu____11277 =
        let uu____11288 =
          let uu____11295 = FStar_TypeChecker_Env.get_range env  in
          let uu____11296 =
            let uu____11313 =
              let uu____11320 =
                let uu____11331 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____11331, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____11320  in
            ([[l_imp_a_b]], [aa; bb], uu____11313)  in
          FStar_SMTEncoding_Term.mkForall uu____11295 uu____11296  in
        (uu____11288, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____11277  in
    [uu____11276]  in
  let mk_iff_interp env iff tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____11643 =
      let uu____11644 =
        let uu____11655 =
          let uu____11662 = FStar_TypeChecker_Env.get_range env  in
          let uu____11663 =
            let uu____11680 =
              let uu____11687 =
                let uu____11698 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____11698, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____11687  in
            ([[l_iff_a_b]], [aa; bb], uu____11680)  in
          FStar_SMTEncoding_Term.mkForall uu____11662 uu____11663  in
        (uu____11655, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____11644  in
    [uu____11643]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____11964 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____11964  in
    let uu____11990 =
      let uu____11991 =
        let uu____12002 =
          let uu____12009 = FStar_TypeChecker_Env.get_range env  in
          let uu____12010 =
            let uu____12027 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____12027)  in
          FStar_SMTEncoding_Term.mkForall uu____12009 uu____12010  in
        (uu____12002, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____11991  in
    [uu____11990]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____12239 =
      let uu____12240 =
        let uu____12251 =
          let uu____12258 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____12258 range_ty  in
        let uu____12265 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____12251, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____12265)
         in
      FStar_SMTEncoding_Util.mkAssume uu____12240  in
    [uu____12239]  in
  let mk_inversion_axiom env inversion tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort)
       in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort)
       in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t])  in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t  in
      let hastypeS =
        let uu____12488 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____12488 x1 t  in
      let uu____12496 = FStar_TypeChecker_Env.get_range env  in
      let uu____12497 =
        let uu____12514 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____12514)  in
      FStar_SMTEncoding_Term.mkForall uu____12496 uu____12497  in
    let uu____12569 =
      let uu____12570 =
        let uu____12581 =
          let uu____12588 = FStar_TypeChecker_Env.get_range env  in
          let uu____12589 =
            let uu____12606 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____12606)  in
          FStar_SMTEncoding_Term.mkForall uu____12588 uu____12589  in
        (uu____12581,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____12570  in
    [uu____12569]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort)
       in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee =
      FStar_SMTEncoding_Term.mk_fv ("e", FStar_SMTEncoding_Term.Term_sort)
       in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____12844 =
      let uu____12845 =
        let uu____12856 =
          let uu____12863 = FStar_TypeChecker_Env.get_range env  in
          let uu____12864 =
            let uu____12886 =
              let uu____12893 =
                let uu____12904 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____12917 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____12904, uu____12917)  in
              FStar_SMTEncoding_Util.mkAnd uu____12893  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____12886)
             in
          FStar_SMTEncoding_Term.mkForall' uu____12863 uu____12864  in
        (uu____12856,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____12845  in
    [uu____12844]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.real_lid, mk_real);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____15765 =
            FStar_Util.find_opt
              (fun uu____15925  ->
                 match uu____15925 with
                 | (l,uu____16002) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____15765 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16228,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____16524 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____16524 with
        | (form,decls) ->
            let uu____16546 =
              let uu____16553 =
                let uu____16556 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____16556]  in
              FStar_All.pipe_right uu____16553
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____16546
  
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____16704 =
                ((let uu____16708 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____16708) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____16704
              then
                let arg_sorts =
                  let uu____16731 =
                    let uu____16732 = FStar_Syntax_Subst.compress t_norm  in
                    uu____16732.FStar_Syntax_Syntax.n  in
                  match uu____16731 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16746) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____16812  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____16824 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____16826 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____16826 with
                | (vname,vtok,env1) ->
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function"))
                       in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function"))
                       in
                    let uu____16902 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____16902, env1)
              else
                (let uu____16918 = prims.is lid  in
                 if uu____16918
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____16938 = prims.mk lid vname  in
                   match uu____16938 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____17007 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____17007, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17027 =
                      let uu____17059 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____17059 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17120 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____17120
                            then
                              let uu____17129 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___295_17140 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___295_17140.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___295_17140.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___295_17140.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___295_17140.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___295_17140.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___295_17140.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___295_17140.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___295_17140.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___295_17140.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___295_17140.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___295_17140.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___295_17140.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___295_17140.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___295_17140.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___295_17140.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___295_17140.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___295_17140.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___295_17140.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___295_17140.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___295_17140.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___295_17140.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___295_17140.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___295_17140.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___295_17140.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___295_17140.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___295_17140.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___295_17140.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___295_17140.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___295_17140.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___295_17140.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___295_17140.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___295_17140.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___295_17140.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___295_17140.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___295_17140.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___295_17140.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___295_17140.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___295_17140.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___295_17140.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___295_17140.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___295_17140.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___295_17140.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17129
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17284 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____17284)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17027 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_17499  ->
                                  match uu___0_17499 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____17507 =
                                        FStar_Util.prefix vars  in
                                      (match uu____17507 with
                                       | (uu____17540,xxv) ->
                                           let xx =
                                             let uu____17585 =
                                               let uu____17586 =
                                                 let uu____17592 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____17592,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____17586
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____17585
                                              in
                                           let uu____17598 =
                                             let uu____17599 =
                                               let uu____17610 =
                                                 let uu____17617 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____17618 =
                                                   let uu____17635 =
                                                     let uu____17642 =
                                                       let uu____17653 =
                                                         let uu____17660 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____17660
                                                          in
                                                       (vapp, uu____17653)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____17642
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____17635)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____17617 uu____17618
                                                  in
                                               (uu____17610,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____17599
                                              in
                                           [uu____17598])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____17726 =
                                        FStar_Util.prefix vars  in
                                      (match uu____17726 with
                                       | (uu____17759,xxv) ->
                                           let xx =
                                             let uu____17804 =
                                               let uu____17805 =
                                                 let uu____17811 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____17811,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____17805
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____17804
                                              in
                                           let f1 =
                                             {
                                               FStar_Syntax_Syntax.ppname = f;
                                               FStar_Syntax_Syntax.index =
                                                 (Prims.parse_int "0");
                                               FStar_Syntax_Syntax.sort =
                                                 FStar_Syntax_Syntax.tun
                                             }  in
                                           let tp_name =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d f1
                                              in
                                           let prim_app =
                                             FStar_SMTEncoding_Util.mkApp
                                               (tp_name, [xx])
                                              in
                                           let uu____17850 =
                                             let uu____17851 =
                                               let uu____17862 =
                                                 let uu____17869 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____17870 =
                                                   let uu____17887 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____17887)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____17869 uu____17870
                                                  in
                                               (uu____17862,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____17851
                                              in
                                           [uu____17850])
                                  | uu____17933 -> []))
                           in
                        let uu____17934 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____17934 with
                         | (vars,guards,env',decls1,uu____17992) ->
                             let uu____18043 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____18074 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____18074, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____18099 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____18099 with
                                    | (g,ds) ->
                                        let uu____18128 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____18128,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____18043 with
                              | (guard,decls11) ->
                                  let dummy_var =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ("@dummy",
                                        FStar_SMTEncoding_Term.dummy_sort)
                                     in
                                  let dummy_tm =
                                    FStar_SMTEncoding_Term.mkFreeV dummy_var
                                      FStar_Range.dummyRange
                                     in
                                  let should_thunk uu____18202 =
                                    let is_type1 t =
                                      let uu____18218 =
                                        let uu____18219 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____18219.FStar_Syntax_Syntax.n  in
                                      match uu____18218 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____18231 -> true
                                      | uu____18233 -> false  in
                                    let is_squash1 t =
                                      let uu____18250 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____18250 with
                                      | (head1,uu____18277) ->
                                          let uu____18318 =
                                            let uu____18319 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____18319.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____18318 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____18335;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____18336;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____18338;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____18339;_};_},uu____18340)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____18370 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____18375 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____18375))
                                       &&
                                       (let uu____18381 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____18381))
                                      &&
                                      (let uu____18384 = is_type1 t_norm  in
                                       Prims.op_Negation uu____18384)
                                     in
                                  let uu____18386 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____18445 -> (false, vars)  in
                                  (match uu____18386 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____18511 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____18511 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____18587 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____18610 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____18610
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____18638 ->
                                                  let uu____18652 =
                                                    let uu____18663 =
                                                      get_vtok ()  in
                                                    (uu____18663, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____18652
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____18688 =
                                                let uu____18699 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____18699)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____18688
                                               in
                                            let uu____18722 =
                                              let vname_decl =
                                                let uu____18745 =
                                                  let uu____18757 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____18757,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____18745
                                                 in
                                              let uu____18768 =
                                                let env2 =
                                                  let uu___390_18799 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___390_18799.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____18822 =
                                                  let uu____18824 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____18824
                                                   in
                                                if uu____18822
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____18768 with
                                              | (tok_typing,decls2) ->
                                                  let uu____18871 =
                                                    match vars1 with
                                                    | [] ->
                                                        let tok_typing1 =
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____18930 =
                                                          let uu____18937 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____18937
                                                           in
                                                        let uu____18956 =
                                                          let uu____18979 =
                                                            let uu____18985 =
                                                              let uu____18992
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____18992
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _19005  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _19005)
                                                              uu____18985
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____18979
                                                           in
                                                        (uu____18930,
                                                          uu____18956)
                                                    | uu____19023 when
                                                        thunked ->
                                                        (decls2, env1)
                                                    | uu____19051 ->
                                                        let vtok =
                                                          get_vtok ()  in
                                                        let vtok_decl =
                                                          FStar_SMTEncoding_Term.DeclFun
                                                            (vtok, [],
                                                              FStar_SMTEncoding_Term.Term_sort,
                                                              FStar_Pervasives_Native.None)
                                                           in
                                                        let name_tok_corr_formula
                                                          pat =
                                                          let uu____19084 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____19085 =
                                                            let uu____19102 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____19102)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____19084
                                                            uu____19085
                                                           in
                                                        let name_tok_corr =
                                                          let uu____19142 =
                                                            let uu____19153 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____19153,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____19142
                                                           in
                                                        let tok_typing1 =
                                                          let ff =
                                                            FStar_SMTEncoding_Term.mk_fv
                                                              ("ty",
                                                                FStar_SMTEncoding_Term.Term_sort)
                                                             in
                                                          let f =
                                                            FStar_SMTEncoding_Util.mkFreeV
                                                              ff
                                                             in
                                                          let vtok_app_r =
                                                            let uu____19185 =
                                                              let uu____19186
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____19186]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____19185
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____19219 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____19220 =
                                                              let uu____19237
                                                                =
                                                                let uu____19244
                                                                  =
                                                                  let uu____19255
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____19262
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____19255,
                                                                    uu____19262)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____19244
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____19237)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____19219
                                                              uu____19220
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____19324 =
                                                          let uu____19331 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____19331
                                                           in
                                                        (uu____19324, env1)
                                                     in
                                                  (match uu____18871 with
                                                   | (tok_decl,env2) ->
                                                       let uu____19424 =
                                                         let uu____19431 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____19431
                                                           tok_decl
                                                          in
                                                       (uu____19424, env2))
                                               in
                                            (match uu____18722 with
                                             | (decls2,env2) ->
                                                 let uu____19518 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____19546 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____19546 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____19580 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____19580, decls)
                                                    in
                                                 (match uu____19518 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____19642 =
                                                          let uu____19653 =
                                                            let uu____19660 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____19661 =
                                                              let uu____19678
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____19678)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____19660
                                                              uu____19661
                                                             in
                                                          (uu____19653,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____19642
                                                         in
                                                      let freshness =
                                                        let uu____19727 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____19727
                                                        then
                                                          let uu____19735 =
                                                            let uu____19736 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____19737 =
                                                              let uu____19750
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____19757
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____19750,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____19757)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____19736
                                                              uu____19737
                                                             in
                                                          let uu____19763 =
                                                            let uu____19766 =
                                                              let uu____19767
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____19767
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____19766]  in
                                                          uu____19735 ::
                                                            uu____19763
                                                        else []  in
                                                      let g =
                                                        let uu____19777 =
                                                          let uu____19784 =
                                                            let uu____19791 =
                                                              let uu____19798
                                                                =
                                                                let uu____19801
                                                                  =
                                                                  let uu____19804
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____19804
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____19801
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____19798
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____19791
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____19784
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____19777
                                                         in
                                                      (g, env2)))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding *
            FStar_SMTEncoding_Term.decls_elt Prims.list *
            FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____19940 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____19940 with
          | FStar_Pervasives_Native.None  ->
              let uu____20000 = encode_free_var false env x t t_norm []  in
              (match uu____20000 with
               | (decls,env1) ->
                   let fvb =
                     FStar_SMTEncoding_Env.lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (fvb, decls, env1))
          | FStar_Pervasives_Native.Some fvb -> (fvb, [], env)
  
let (encode_top_level_val :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm_before_encoding env t  in
            let uu____20274 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____20274 with
            | (decls,env1) ->
                let uu____20329 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____20329
                then
                  let uu____20347 =
                    let uu____20348 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____20348  in
                  (uu____20347, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_elt Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____20529  ->
                fun lb  ->
                  match uu____20529 with
                  | (decls,env1) ->
                      let uu____20616 =
                        let uu____20632 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____20632
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____20616 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____20766 = FStar_Syntax_Util.head_and_args t  in
    match uu____20766 with
    | (hd1,args) ->
        let uu____20834 =
          let uu____20835 = FStar_Syntax_Util.un_uinst hd1  in
          uu____20835.FStar_Syntax_Syntax.n  in
        (match uu____20834 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____20852,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____20902 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____20913 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___474_20954 = en  in
    let uu____20977 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___474_20954.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___474_20954.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___474_20954.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___474_20954.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___474_20954.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___474_20954.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___474_20954.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___474_20954.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___474_20954.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___474_20954.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____20977
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____21044  ->
      fun quals  ->
        match uu____21044 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____21242 = FStar_Util.first_N nbinders formals  in
              match uu____21242 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____21393  ->
                         fun uu____21394  ->
                           match (uu____21393, uu____21394) with
                           | ((formal,uu____21440),(binder,uu____21442)) ->
                               let uu____21493 =
                                 let uu____21509 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____21509)  in
                               FStar_Syntax_Syntax.NT uu____21493) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____21545 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____21611  ->
                              match uu____21611 with
                              | (x,i) ->
                                  let uu____21650 =
                                    let uu___500_21661 = x  in
                                    let uu____21672 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___500_21661.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___500_21661.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____21672
                                    }  in
                                  (uu____21650, i)))
                       in
                    FStar_All.pipe_right uu____21545
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____21727 =
                      let uu____21732 = FStar_Syntax_Subst.compress body  in
                      let uu____21741 =
                        let uu____21742 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____21742
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____21732
                        uu____21741
                       in
                    uu____21727 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___507_21945 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___507_21945.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___507_21945.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___507_21945.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___507_21945.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___507_21945.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___507_21945.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___507_21945.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___507_21945.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___507_21945.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___507_21945.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___507_21945.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___507_21945.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___507_21945.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___507_21945.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___507_21945.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___507_21945.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___507_21945.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___507_21945.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___507_21945.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___507_21945.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___507_21945.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___507_21945.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___507_21945.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___507_21945.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___507_21945.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___507_21945.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___507_21945.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___507_21945.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___507_21945.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___507_21945.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___507_21945.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___507_21945.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___507_21945.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___507_21945.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___507_21945.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___507_21945.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___507_21945.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___507_21945.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___507_21945.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___507_21945.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___507_21945.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___507_21945.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____22167  ->
                       fun uu____22168  ->
                         match (uu____22167, uu____22168) with
                         | ((x,uu____22214),(b,uu____22216)) ->
                             let uu____22267 =
                               let uu____22283 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____22283)  in
                             FStar_Syntax_Syntax.NT uu____22267) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____22345 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____22345
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____22412 ->
                    let uu____22428 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____22428
                | uu____22437 when Prims.op_Negation norm1 ->
                    let t_norm =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Exclude
                          FStar_TypeChecker_Env.Zeta;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.EraseUniverses] tcenv t2
                       in
                    arrow_formals_comp_norm true t_norm
                | uu____22448 ->
                    let uu____22449 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____22449)
                 in
              let aux t1 e1 =
                let uu____22542 = FStar_Syntax_Util.abs_formals e1  in
                match uu____22542 with
                | (binders,body,lopt) ->
                    let uu____22620 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____22649 -> arrow_formals_comp_norm false t1  in
                    (match uu____22620 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____22714 =
                           if nformals < nbinders
                           then
                             let uu____22774 =
                               FStar_Util.first_N nformals binders  in
                             match uu____22774 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____22910 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____22910)
                           else
                             if nformals > nbinders
                             then
                               (let uu____22974 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____22974 with
                                | (binders1,body1) ->
                                    let uu____23067 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____23067))
                             else
                               (let uu____23101 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____23101))
                            in
                         (match uu____22714 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____23234 = aux t e  in
              match uu____23234 with
              | (binders,body,comp) ->
                  let uu____23327 =
                    let uu____23346 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____23346
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____23385 = aux comp1 body1  in
                      match uu____23385 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____23327 with
                   | (binders1,body1,comp1) ->
                       let uu____23560 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____23560, comp1))
               in
            (try
               (fun uu___577_23642  ->
                  match () with
                  | () ->
                      let uu____23664 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____23664
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____23716 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____23880  ->
                                   fun lb  ->
                                     match uu____23880 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____24058 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____24058
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____24072 =
                                             let uu____24106 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____24106
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____24072 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____23716 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____24692;
                                    FStar_Syntax_Syntax.lbeff = uu____24693;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____24695;
                                    FStar_Syntax_Syntax.lbpos = uu____24696;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____24831 =
                                     let uu____24857 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____24857 with
                                     | (tcenv',uu____24962,e_t) ->
                                         let uu____25084 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____25139 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____25084 with
                                          | (e1,t_norm1) ->
                                              ((let uu___640_25222 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___640_25222.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____24831 with
                                    | (env',e1,t_norm1) ->
                                        let uu____25307 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____25307 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____25374 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____25374
                                               then
                                                 let uu____25379 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____25382 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____25379 uu____25382
                                               else ());
                                              (let uu____25387 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____25387 with
                                               | (vars,_guards,env'1,binder_decls,uu____25451)
                                                   ->
                                                   let uu____25502 =
                                                     if
                                                       fvb.FStar_SMTEncoding_Env.fvb_thunked
                                                         && (vars = [])
                                                     then
                                                       let dummy_var =
                                                         FStar_SMTEncoding_Term.mk_fv
                                                           ("@dummy",
                                                             FStar_SMTEncoding_Term.dummy_sort)
                                                          in
                                                       let dummy_tm =
                                                         FStar_SMTEncoding_Term.mkFreeV
                                                           dummy_var
                                                           FStar_Range.dummyRange
                                                          in
                                                       let app =
                                                         let uu____25537 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____25537
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____25571 =
                                                          let uu____25578 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____25579 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____25578 fvb
                                                            uu____25579
                                                           in
                                                        (vars, uu____25571))
                                                      in
                                                   (match uu____25502 with
                                                    | (vars1,app) ->
                                                        let uu____25620 =
                                                          let is_logical =
                                                            let uu____25642 =
                                                              let uu____25643
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____25643.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____25642
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____25660 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____25664 =
                                                              let uu____25673
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____25673
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____25664
                                                              (fun lid  ->
                                                                 let uu____25722
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____25722
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____25731 =
                                                            (Prims.op_Negation
                                                               is_prims)
                                                              &&
                                                              ((FStar_All.pipe_right
                                                                  quals
                                                                  (FStar_List.contains
                                                                    FStar_Syntax_Syntax.Logic))
                                                                 ||
                                                                 is_logical)
                                                             in
                                                          if uu____25731
                                                          then
                                                            let uu____25756 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____25763 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____25756,
                                                              uu____25763)
                                                          else
                                                            (let uu____25786
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____25786))
                                                           in
                                                        (match uu____25620
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____25858
                                                                 =
                                                                 let uu____25869
                                                                   =
                                                                   let uu____25876
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____25877
                                                                    =
                                                                    let uu____25894
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____25894)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____25876
                                                                    uu____25877
                                                                    in
                                                                 let uu____25933
                                                                   =
                                                                   let uu____25934
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____25934
                                                                    in
                                                                 (uu____25869,
                                                                   uu____25933,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____25858
                                                                in
                                                             let uu____25943
                                                               =
                                                               let uu____25950
                                                                 =
                                                                 let uu____25957
                                                                   =
                                                                   let uu____25964
                                                                    =
                                                                    let uu____25971
                                                                    =
                                                                    let uu____25974
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____25974
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25971
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____25964
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____25957
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____25950
                                                                in
                                                             (uu____25943,
                                                               env2)))))))
                               | uu____26014 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____26189 =
                                   let uu____26195 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____26195,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____26189  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____26229 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____26365  ->
                                         fun fvb  ->
                                           match uu____26365 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____26522 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____26522
                                                  in
                                               let gtok =
                                                 let uu____26534 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____26534
                                                  in
                                               let env4 =
                                                 let uu____26567 =
                                                   let uu____26573 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _26603  ->
                                                        FStar_Pervasives_Native.Some
                                                          _26603) uu____26573
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____26567
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____26229 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____26919
                                     t_norm uu____26921 =
                                     match (uu____26919, uu____26921) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____27015;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____27016;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____27018;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____27019;_})
                                         ->
                                         let uu____27109 =
                                           let uu____27135 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____27135 with
                                           | (tcenv',uu____27240,e_t) ->
                                               let uu____27362 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____27417 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____27362 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___727_27500 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___727_27500.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____27109 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____27588 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____27588
                                                then
                                                  let uu____27593 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____27595 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____27597 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____27593 uu____27595
                                                    uu____27597
                                                else ());
                                               (let uu____27602 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____27602 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____27673 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____27673 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____27734 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____27734
                                                           then
                                                             let uu____27739
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____27741
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____27744
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____27746
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____27739
                                                               uu____27741
                                                               uu____27744
                                                               uu____27746
                                                           else ());
                                                          (let uu____27751 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____27751
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____27817)
                                                               ->
                                                               let uu____27868
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____27899
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____27899,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____27928
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____27928
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____27957
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____27957,
                                                                    decls0))
                                                                  in
                                                               (match uu____27868
                                                                with
                                                                | (guard,guard_decls)
                                                                    ->
                                                                    let binder_decls1
                                                                    =
                                                                    FStar_List.append
                                                                    binder_decls
                                                                    guard_decls
                                                                     in
                                                                    let decl_g
                                                                    =
                                                                    let uu____28037
                                                                    =
                                                                    let uu____28049
                                                                    =
                                                                    let uu____28052
                                                                    =
                                                                    let uu____28055
                                                                    =
                                                                    let uu____28058
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____28058
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____28055
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____28052
                                                                     in
                                                                    (g,
                                                                    uu____28049,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____28037
                                                                     in
                                                                    let env02
                                                                    =
                                                                    FStar_SMTEncoding_Env.push_zfuel_name
                                                                    env01
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                                    g  in
                                                                    let decl_g_tok
                                                                    =
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    (gtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Token for fuel-instrumented partial applications"))
                                                                     in
                                                                    let vars_tm
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    let rng =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let app =
                                                                    let uu____28122
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____28122
                                                                     in
                                                                    let mk_g_app
                                                                    args =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    rng
                                                                    (FStar_Util.Inl
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    g))
                                                                    (fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    +
                                                                    (Prims.parse_int "1"))
                                                                    args  in
                                                                    let gsapp
                                                                    =
                                                                    let uu____28161
                                                                    =
                                                                    let uu____28167
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____28167
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____28161
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____28197
                                                                    =
                                                                    let uu____28203
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____28203
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____28197
                                                                     in
                                                                    let uu____28223
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____28223
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____28263
                                                                    =
                                                                    let uu____28274
                                                                    =
                                                                    let uu____28281
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____28282
                                                                    =
                                                                    let uu____28304
                                                                    =
                                                                    let uu____28311
                                                                    =
                                                                    let uu____28322
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____28322)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____28311
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____28304)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____28281
                                                                    uu____28282
                                                                     in
                                                                    let uu____28372
                                                                    =
                                                                    let uu____28373
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____28373
                                                                     in
                                                                    (uu____28274,
                                                                    uu____28372,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____28263
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____28383
                                                                    =
                                                                    let uu____28394
                                                                    =
                                                                    let uu____28401
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____28402
                                                                    =
                                                                    let uu____28419
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____28419)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____28401
                                                                    uu____28402
                                                                     in
                                                                    (uu____28394,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____28383
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____28466
                                                                    =
                                                                    let uu____28477
                                                                    =
                                                                    let uu____28484
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____28485
                                                                    =
                                                                    let uu____28502
                                                                    =
                                                                    let uu____28509
                                                                    =
                                                                    let uu____28520
                                                                    =
                                                                    let uu____28527
                                                                    =
                                                                    let uu____28533
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____28533
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____28527
                                                                     in
                                                                    (gsapp,
                                                                    uu____28520)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____28509
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____28502)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____28484
                                                                    uu____28485
                                                                     in
                                                                    (uu____28477,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____28466
                                                                     in
                                                                    let uu____28583
                                                                    =
                                                                    let gapp
                                                                    =
                                                                    mk_g_app
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm)
                                                                     in
                                                                    let tok_corr
                                                                    =
                                                                    let tok_app
                                                                    =
                                                                    let uu____28614
                                                                    =
                                                                    let uu____28621
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____28621
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____28614
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____28626
                                                                    =
                                                                    let uu____28637
                                                                    =
                                                                    let uu____28644
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____28645
                                                                    =
                                                                    let uu____28662
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____28662)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____28644
                                                                    uu____28645
                                                                     in
                                                                    (uu____28637,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____28626
                                                                     in
                                                                    let uu____28708
                                                                    =
                                                                    let uu____28721
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____28721
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____28752
                                                                    =
                                                                    let uu____28755
                                                                    =
                                                                    let uu____28756
                                                                    =
                                                                    let uu____28767
                                                                    =
                                                                    let uu____28774
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____28775
                                                                    =
                                                                    let uu____28792
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____28792)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____28774
                                                                    uu____28775
                                                                     in
                                                                    (uu____28767,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____28756
                                                                     in
                                                                    [uu____28755]
                                                                     in
                                                                    (d3,
                                                                    uu____28752)
                                                                     in
                                                                    match uu____28708
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____28583
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____28925
                                                                    =
                                                                    let uu____28932
                                                                    =
                                                                    let uu____28939
                                                                    =
                                                                    let uu____28946
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____28946
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____28939
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____28932
                                                                     in
                                                                    let uu____28973
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____28925,
                                                                    uu____28973,
                                                                    env02))))))))))
                                      in
                                   let uu____28993 =
                                     let uu____29025 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____29170  ->
                                          fun uu____29171  ->
                                            match (uu____29170, uu____29171)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____29515 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____29515 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____29025
                                      in
                                   (match uu____28993 with
                                    | (decls2,eqns,env01) ->
                                        let uu____29757 =
                                          let isDeclFun uu___1_29782 =
                                            match uu___1_29782 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____29784 -> true
                                            | uu____29797 -> false  in
                                          let uu____29799 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____29799
                                            (fun decls3  ->
                                               let uu____29861 =
                                                 FStar_List.fold_left
                                                   (fun uu____29912  ->
                                                      fun elt  ->
                                                        match uu____29912
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____29989 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____29989
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____30045
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____30045
                                                               with
                                                               | (elt_decl_funs,elt_rest)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    prefix_decls
                                                                    elt_decl_funs),
                                                                    elts,
                                                                    (FStar_List.append
                                                                    rest
                                                                    [(
                                                                    let uu___820_30107
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___820_30107.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___820_30107.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___820_30107.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____29861 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____30191 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____30191, elts, rest))
                                           in
                                        (match uu____29757 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____30294 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_30300  ->
                                        match uu___2_30300 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____30303 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____30323 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____30323)))
                                in
                             if uu____30294
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___837_30390  ->
                                     match () with
                                     | () ->
                                         if Prims.op_Negation is_rec
                                         then
                                           encode_non_rec_lbdef bindings
                                             typs1 toks_fvbs env1
                                         else
                                           encode_rec_lbdefs bindings typs1
                                             toks_fvbs env1) ()
                                with
                                | FStar_SMTEncoding_Env.Inner_let_rec  ->
                                    (decls1, env_decls)))) ()
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____30504 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____30504
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____30544 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____30544, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____30731 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____30731 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____30753 = encode_sigelt' env se  in
      match uu____30753 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____30813 =
                  let uu____30816 =
                    let uu____30817 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____30817  in
                  [uu____30816]  in
                FStar_All.pipe_right uu____30813
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____30822 ->
                let uu____30823 =
                  let uu____30830 =
                    let uu____30833 =
                      let uu____30834 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____30834  in
                    [uu____30833]  in
                  FStar_All.pipe_right uu____30830
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____30845 =
                  let uu____30852 =
                    let uu____30859 =
                      let uu____30862 =
                        let uu____30863 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____30863  in
                      [uu____30862]  in
                    FStar_All.pipe_right uu____30859
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____30852  in
                FStar_List.append uu____30823 uu____30845
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____30927 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____30927
       then
         let uu____30932 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____30932
       else ());
      (let is_opaque_to_smt t =
         let uu____30952 =
           let uu____30953 = FStar_Syntax_Subst.compress t  in
           uu____30953.FStar_Syntax_Syntax.n  in
         match uu____30952 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____30966)) -> s = "opaque_to_smt"
         | uu____30971 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____30988 =
           let uu____30989 = FStar_Syntax_Subst.compress t  in
           uu____30989.FStar_Syntax_Syntax.n  in
         match uu____30988 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____31002)) -> s = "uninterpreted_by_smt"
         | uu____31007 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____31024 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____31061 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____31092 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____31108 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____31128 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____31164 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____31209 =
             let uu____31211 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____31211  in
           if uu____31209
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____31287 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_abs
                         ((ed.FStar_Syntax_Syntax.binders), tm,
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                 in
              let encode_action env1 a =
                let action_defn =
                  let uu____31412 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____31412  in
                let uu____31421 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____31421 with
                | (formals,uu____31465) ->
                    let arity = FStar_List.length formals  in
                    let uu____31512 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____31512 with
                     | (aname,atok,env2) ->
                         let uu____31582 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____31582 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____31622 =
                                  let uu____31623 =
                                    let uu____31635 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____31665  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____31635,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____31623
                                   in
                                [uu____31622;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____31687 =
                                let aux uu____31780 uu____31781 =
                                  match (uu____31780, uu____31781) with
                                  | ((bv,uu____31877),(env3,acc_sorts,acc))
                                      ->
                                      let uu____31966 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____31966 with
                                       | (xxsym,xx,env4) ->
                                           let uu____32045 =
                                             let uu____32048 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____32048 :: acc_sorts  in
                                           (env4, uu____32045, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____31687 with
                               | (uu____32148,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____32201 =
                                       let uu____32212 =
                                         let uu____32219 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____32220 =
                                           let uu____32237 =
                                             let uu____32244 =
                                               let uu____32255 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____32255)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____32244
                                              in
                                           ([[app]], xs_sorts, uu____32237)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____32219 uu____32220
                                          in
                                       (uu____32212,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____32201
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____32309 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____32309
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____32321 =
                                       let uu____32332 =
                                         let uu____32339 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____32340 =
                                           let uu____32357 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____32357)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____32339 uu____32340
                                          in
                                       (uu____32332,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____32321
                                      in
                                   let uu____32403 =
                                     let uu____32410 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____32410  in
                                   (env2, uu____32403))))
                 in
              let uu____32446 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____32446 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____32568,uu____32569)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____32586 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____32586 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____32667,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____32690 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_32696  ->
                       match uu___3_32696 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____32699 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____32711 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____32718 -> false))
                in
             Prims.op_Negation uu____32690  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____32760 =
                let uu____32776 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____32776 env fv t quals  in
              match uu____32760 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____32837 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____32837  in
                  let uu____32846 =
                    let uu____32847 =
                      let uu____32854 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____32854
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____32847  in
                  (uu____32846, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____32899 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____32899 with
            | (uvs,f1) ->
                let env1 =
                  let uu___974_32956 = env  in
                  let uu____32979 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___974_32956.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___974_32956.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___974_32956.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____32979;
                    FStar_SMTEncoding_Env.warn =
                      (uu___974_32956.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___974_32956.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___974_32956.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___974_32956.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___974_32956.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___974_32956.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___974_32956.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____33097 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____33097 with
                 | (f3,decls) ->
                     let g =
                       let uu____33135 =
                         let uu____33138 =
                           let uu____33139 =
                             let uu____33150 =
                               let uu____33151 =
                                 let uu____33153 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____33153
                                  in
                               FStar_Pervasives_Native.Some uu____33151  in
                             let uu____33157 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____33150, uu____33157)  in
                           FStar_SMTEncoding_Util.mkAssume uu____33139  in
                         [uu____33138]  in
                       FStar_All.pipe_right uu____33135
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____33188) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____33222 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____33307 =
                        let uu____33317 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____33317.FStar_Syntax_Syntax.fv_name  in
                      uu____33307.FStar_Syntax_Syntax.v  in
                    let uu____33336 =
                      let uu____33338 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____33338  in
                    if uu____33336
                    then
                      let val_decl =
                        let uu___991_33395 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___991_33395.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___991_33395.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___991_33395.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____33414 = encode_sigelt' env1 val_decl  in
                      match uu____33414 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____33222 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____33595,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____33597;
                           FStar_Syntax_Syntax.lbtyp = uu____33598;
                           FStar_Syntax_Syntax.lbeff = uu____33599;
                           FStar_Syntax_Syntax.lbdef = uu____33600;
                           FStar_Syntax_Syntax.lbattrs = uu____33601;
                           FStar_Syntax_Syntax.lbpos = uu____33602;_}::[]),uu____33603)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____33680 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____33680 with
            | (tname,ttok,env1) ->
                let xx =
                  FStar_SMTEncoding_Term.mk_fv
                    ("x", FStar_SMTEncoding_Term.Term_sort)
                   in
                let x = FStar_SMTEncoding_Util.mkFreeV xx  in
                let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                   in
                let valid_b2t_x =
                  FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
                let decls =
                  let uu____33802 =
                    let uu____33805 =
                      let uu____33806 =
                        let uu____33817 =
                          let uu____33824 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____33825 =
                            let uu____33842 =
                              let uu____33849 =
                                let uu____33860 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____33860)  in
                              FStar_SMTEncoding_Util.mkEq uu____33849  in
                            ([[b2t_x]], [xx], uu____33842)  in
                          FStar_SMTEncoding_Term.mkForall uu____33824
                            uu____33825
                           in
                        (uu____33817,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____33806  in
                    [uu____33805]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____33802
                   in
                let uu____33940 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____33940, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____33954,uu____33955) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_33973  ->
                   match uu___4_33973 with
                   | FStar_Syntax_Syntax.Discriminator uu____33975 -> true
                   | uu____33981 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____33998,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____34030 =
                      let uu____34032 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____34032.FStar_Ident.idText  in
                    uu____34030 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_34045  ->
                      match uu___5_34045 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____34048 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____34066) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_34116  ->
                   match uu___6_34116 with
                   | FStar_Syntax_Syntax.Projector uu____34118 -> true
                   | uu____34130 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____34160 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____34160 with
            | FStar_Pervasives_Native.Some uu____34181 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1056_34217 = se  in
                  let uu____34228 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____34228;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1056_34217.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1056_34217.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1056_34217.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____34239) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1068_34326 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1068_34326.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1068_34326.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1068_34326.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1068_34326.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1068_34326.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____34352) ->
           let uu____34379 = encode_sigelts env ses  in
           (match uu____34379 with
            | (g,env1) ->
                let uu____34434 =
                  FStar_List.fold_left
                    (fun uu____34470  ->
                       fun elt  ->
                         match uu____34470 with
                         | (g',inversions) ->
                             let uu____34518 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_34541  ->
                                       match uu___7_34541 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____34543;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____34544;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____34545;_}
                                           -> false
                                       | uu____34555 -> true))
                                in
                             (match uu____34518 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1094_34596 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1094_34596.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1094_34596.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1094_34596.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____34434 with
                 | (g',inversions) ->
                     let uu____34654 =
                       FStar_List.fold_left
                         (fun uu____34705  ->
                            fun elt  ->
                              match uu____34705 with
                              | (decls,elts,rest) ->
                                  let uu____34782 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_34791  ->
                                            match uu___8_34791 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____34793 -> true
                                            | uu____34806 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____34782
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____34857 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_34878  ->
                                               match uu___9_34878 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____34880 -> true
                                               | uu____34893 -> false))
                                        in
                                     match uu____34857 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1116_34948 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1116_34948.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1116_34948.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1116_34948.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____34654 with
                      | (decls,elts,rest) ->
                          let uu____35029 =
                            let uu____35030 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____35045 =
                              let uu____35052 =
                                let uu____35059 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____35059  in
                              FStar_List.append elts uu____35052  in
                            FStar_List.append uu____35030 uu____35045  in
                          (uu____35029, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____35101,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____35254 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____35254 with
             | (usubst,uvs) ->
                 let uu____35280 =
                   let uu____35345 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____35454 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____35455 =
                     let uu____35464 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____35464 k  in
                   (uu____35345, uu____35454, uu____35455)  in
                 (match uu____35280 with
                  | (env1,tps1,k1) ->
                      let uu____35656 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____35656 with
                       | (tps2,k2) ->
                           let uu____35676 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____35676 with
                            | (uu____35701,k3) ->
                                let uu____35741 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____35741 with
                                 | (tps3,env_tps,uu____35811,us) ->
                                     let u_k =
                                       let uu____35930 =
                                         let uu____35939 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____35940 =
                                           let uu____35945 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____35955 =
                                             let uu____35956 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____35956
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____35945 uu____35955
                                            in
                                         uu____35940
                                           FStar_Pervasives_Native.None
                                           uu____35939
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____35930 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____35974) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____35984,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____35989) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____35997,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____36004) ->
                                           let uu____36005 =
                                             let uu____36007 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____36007
                                              in
                                           failwith uu____36005
                                       | (uu____36011,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____36012 =
                                             let uu____36014 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____36014
                                              in
                                           failwith uu____36012
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____36018,uu____36019) ->
                                           let uu____36030 =
                                             let uu____36032 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____36032
                                              in
                                           failwith uu____36030
                                       | (uu____36036,FStar_Syntax_Syntax.U_unif
                                          uu____36037) ->
                                           let uu____36048 =
                                             let uu____36050 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____36050
                                              in
                                           failwith uu____36048
                                       | uu____36054 -> false  in
                                     let u_leq_u_k u =
                                       let uu____36067 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____36067 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____36098 = u_leq_u_k u_tp  in
                                       if uu____36098
                                       then true
                                       else
                                         (let uu____36105 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____36105 with
                                          | (formals,uu____36131) ->
                                              let uu____36170 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____36170 with
                                               | (uu____36238,uu____36239,uu____36240,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____36372 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____36372
             then
               let uu____36377 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____36377
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_36397  ->
                       match uu___10_36397 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____36401 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____36414 = c  in
                 match uu____36414 with
                 | (name,args,uu____36419,uu____36420,uu____36421) ->
                     let uu____36432 =
                       let uu____36433 =
                         let uu____36445 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____36472  ->
                                   match uu____36472 with
                                   | (uu____36481,sort,uu____36483) -> sort))
                            in
                         (name, uu____36445,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____36433  in
                     [uu____36432]
               else
                 (let uu____36494 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____36494 c)
                in
             let inversion_axioms tapp vars =
               let uu____36522 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____36542 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____36542 FStar_Option.isNone))
                  in
               if uu____36522
               then []
               else
                 (let uu____36597 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____36597 with
                  | (xxsym,xx) ->
                      let uu____36623 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____36691  ->
                                fun l  ->
                                  match uu____36691 with
                                  | (out,decls) ->
                                      let uu____36743 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____36743 with
                                       | (uu____36765,data_t) ->
                                           let uu____36775 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____36775 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____36853 =
                                                    let uu____36854 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____36854.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____36853 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____36865,indices)
                                                      -> indices
                                                  | uu____36907 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____36995  ->
                                                            match uu____36995
                                                            with
                                                            | (x,uu____37030)
                                                                ->
                                                                let uu____37045
                                                                  =
                                                                  let uu____37052
                                                                    =
                                                                    let uu____37063
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____37063,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____37052
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____37045)
                                                       env)
                                                   in
                                                let uu____37077 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____37077 with
                                                 | (indices1,decls') ->
                                                     (if
                                                        (FStar_List.length
                                                           indices1)
                                                          <>
                                                          (FStar_List.length
                                                             vars)
                                                      then
                                                        failwith "Impossible"
                                                      else ();
                                                      (let eqs =
                                                         if is_injective
                                                         then
                                                           FStar_List.map2
                                                             (fun v1  ->
                                                                fun a  ->
                                                                  let uu____37146
                                                                    =
                                                                    let uu____37157
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____37157,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____37146)
                                                             vars indices1
                                                         else []  in
                                                       let uu____37175 =
                                                         let uu____37182 =
                                                           let uu____37193 =
                                                             let uu____37200
                                                               =
                                                               let uu____37211
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____37229
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____37211,
                                                                 uu____37229)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____37200
                                                              in
                                                           (out, uu____37193)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____37182
                                                          in
                                                       (uu____37175,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____36623 with
                       | (data_ax,decls) ->
                           let uu____37308 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____37308 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____37351 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____37351 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____37373 =
                                    let uu____37384 =
                                      let uu____37391 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____37392 =
                                        let uu____37409 =
                                          let uu____37410 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____37412 =
                                            let uu____37415 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____37415 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____37410 uu____37412
                                           in
                                        let uu____37417 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____37409,
                                          uu____37417)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____37391 uu____37392
                                       in
                                    let uu____37456 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____37384,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____37456)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____37373
                                   in
                                let uu____37465 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____37465)))
                in
             let uu____37484 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____37532 ->
                     let uu____37533 =
                       let uu____37540 =
                         let uu____37541 =
                           let uu____37565 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____37565)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____37541  in
                       FStar_Syntax_Syntax.mk uu____37540  in
                     uu____37533 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____37484 with
             | (formals,res) ->
                 let uu____37659 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____37659 with
                  | (vars,guards,env',binder_decls,uu____37717) ->
                      let arity = FStar_List.length vars  in
                      let uu____37769 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____37769 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____37863 =
                               let uu____37874 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____37874)  in
                             FStar_SMTEncoding_Util.mkApp uu____37863  in
                           let uu____37889 =
                             let tname_decl =
                               let uu____37910 =
                                 let uu____37911 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____37930 =
                                             let uu____37932 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____37932
                                              in
                                           let uu____37934 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____37930, uu____37934, false)))
                                    in
                                 let uu____37938 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____37911,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____37938, false)
                                  in
                               constructor_or_logic_type_decl uu____37910  in
                             let uu____37946 =
                               match vars with
                               | [] ->
                                   let uu____37981 =
                                     let uu____38004 =
                                       let uu____38010 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _38037  ->
                                            FStar_Pervasives_Native.Some
                                              _38037) uu____38010
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____38004
                                      in
                                   ([], uu____37981)
                               | uu____38051 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____38061 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____38061
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____38107 =
                                       let uu____38118 =
                                         let uu____38125 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____38126 =
                                           let uu____38148 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____38148)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____38125 uu____38126
                                          in
                                       (uu____38118,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____38107
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____37946 with
                             | (tok_decls,env2) ->
                                 let uu____38240 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____38240
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____37889 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____38338 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____38338 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____38381 =
                                            let uu____38382 =
                                              let uu____38393 =
                                                let uu____38400 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____38400
                                                 in
                                              (uu____38393,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____38382
                                             in
                                          [uu____38381]
                                        else []  in
                                      let uu____38417 =
                                        let uu____38424 =
                                          let uu____38427 =
                                            let uu____38430 =
                                              let uu____38431 =
                                                let uu____38442 =
                                                  let uu____38449 =
                                                    FStar_Ident.range_of_lid
                                                      t
                                                     in
                                                  let uu____38450 =
                                                    let uu____38467 =
                                                      FStar_SMTEncoding_Util.mkImp
                                                        (guard, k1)
                                                       in
                                                    ([[tapp]], vars,
                                                      uu____38467)
                                                     in
                                                  FStar_SMTEncoding_Term.mkForall
                                                    uu____38449 uu____38450
                                                   in
                                                (uu____38442,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____38431
                                               in
                                            [uu____38430]  in
                                          FStar_List.append karr uu____38427
                                           in
                                        FStar_All.pipe_right uu____38424
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____38417
                                   in
                                let aux =
                                  let uu____38531 =
                                    let uu____38538 =
                                      inversion_axioms tapp vars  in
                                    let uu____38545 =
                                      let uu____38552 =
                                        let uu____38555 =
                                          let uu____38556 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____38556 env2 tapp
                                            vars
                                           in
                                        [uu____38555]  in
                                      FStar_All.pipe_right uu____38552
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____38538 uu____38545
                                     in
                                  FStar_List.append kindingAx uu____38531  in
                                let g =
                                  let uu____38580 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____38580
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____38615,uu____38616,uu____38617,uu____38618,uu____38619)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____38674,t,uu____38676,n_tps,uu____38678) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____38729 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____38729 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____38820 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____38820 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____38900 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____38900 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____38955 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____38955 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____39120 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____39120,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____39127 =
                                   let uu____39128 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____39128, true)
                                    in
                                 let uu____39136 =
                                   let uu____39143 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____39143
                                    in
                                 FStar_All.pipe_right uu____39127 uu____39136
                                  in
                               let app =
                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                   ddtok_tm vars
                                  in
                               let guard =
                                 FStar_SMTEncoding_Util.mk_and_l guards  in
                               let xvars =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               let dapp =
                                 FStar_SMTEncoding_Util.mkApp
                                   (ddconstrsym, xvars)
                                  in
                               let uu____39182 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____39182 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____39226::uu____39227 ->
                                          let ff =
                                            FStar_SMTEncoding_Term.mk_fv
                                              ("ty",
                                                FStar_SMTEncoding_Term.Term_sort)
                                             in
                                          let f =
                                            FStar_SMTEncoding_Util.mkFreeV ff
                                             in
                                          let vtok_app_l =
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              ddtok_tm [ff]
                                             in
                                          let vtok_app_r =
                                            let uu____39294 =
                                              let uu____39295 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____39295]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____39294
                                             in
                                          let uu____39321 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____39322 =
                                            let uu____39339 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____39339)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____39321 uu____39322
                                      | uu____39399 -> tok_typing  in
                                    let uu____39410 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____39410 with
                                     | (vars',guards',env'',decls_formals,uu____39468)
                                         ->
                                         let uu____39519 =
                                           let xvars1 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars'
                                              in
                                           let dapp1 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (ddconstrsym, xvars1)
                                              in
                                           FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                             (FStar_Pervasives_Native.Some
                                                fuel_tm) t_res env'' dapp1
                                            in
                                         (match uu____39519 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____39598 ->
                                                    let uu____39612 =
                                                      let uu____39613 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____39613
                                                       in
                                                    [uu____39612]
                                                 in
                                              let encode_elim uu____39633 =
                                                let uu____39634 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____39634 with
                                                | (head1,args) ->
                                                    let uu____39713 =
                                                      let uu____39714 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____39714.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____39713 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____39738;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____39739;_},uu____39740)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____39777 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____39777
                                                          with
                                                          | (encoded_args,arg_decls)
                                                              ->
                                                              let guards_for_parameter
                                                                orig_arg arg
                                                                xv =
                                                                let fv1 =
                                                                  match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                  with
                                                                  | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                  | uu____39876
                                                                    ->
                                                                    let uu____39877
                                                                    =
                                                                    let uu____39883
                                                                    =
                                                                    let uu____39885
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____39885
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____39883)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____39877
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____39926
                                                                    =
                                                                    let uu____39928
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____39928
                                                                     in
                                                                    if
                                                                    uu____39926
                                                                    then
                                                                    let uu____39953
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____39953]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____39971
                                                                =
                                                                let uu____40002
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____40097
                                                                     ->
                                                                    fun
                                                                    uu____40098
                                                                     ->
                                                                    match 
                                                                    (uu____40097,
                                                                    uu____40098)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____40346
                                                                    =
                                                                    let uu____40368
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____40368
                                                                     in
                                                                    (match uu____40346
                                                                    with
                                                                    | 
                                                                    (uu____40409,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____40454
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____40454
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____40472
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____40472
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                  (env', [],
                                                                    [],
                                                                    (Prims.parse_int "0"))
                                                                  uu____40002
                                                                 in
                                                              (match uu____39971
                                                               with
                                                               | (uu____40555,arg_vars,elim_eqns_or_guards,uu____40558)
                                                                   ->
                                                                   let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                   let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
                                                                    arg_vars1
                                                                     in
                                                                   let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                   let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                   let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                   let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                   let typing_inversion
                                                                    =
                                                                    let uu____40662
                                                                    =
                                                                    let uu____40673
                                                                    =
                                                                    let uu____40680
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____40681
                                                                    =
                                                                    let uu____40698
                                                                    =
                                                                    let uu____40699
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____40699
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____40701
                                                                    =
                                                                    let uu____40708
                                                                    =
                                                                    let uu____40719
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____40719)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____40708
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____40698,
                                                                    uu____40701)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____40680
                                                                    uu____40681
                                                                     in
                                                                    (uu____40673,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____40662
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____40776
                                                                    =
                                                                    let uu____40777
                                                                    =
                                                                    let uu____40783
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____40783,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____40777
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____40776
                                                                     in
                                                                    let uu____40789
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____40789
                                                                    then
                                                                    let x =
                                                                    let uu____40793
                                                                    =
                                                                    let uu____40799
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____40799,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____40793
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____40810
                                                                    =
                                                                    let uu____40821
                                                                    =
                                                                    let uu____40828
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____40829
                                                                    =
                                                                    let uu____40846
                                                                    =
                                                                    let uu____40854
                                                                    =
                                                                    let uu____40860
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____40860]
                                                                     in
                                                                    [uu____40854]
                                                                     in
                                                                    let uu____40883
                                                                    =
                                                                    let uu____40890
                                                                    =
                                                                    let uu____40901
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____40909
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____40901,
                                                                    uu____40909)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____40890
                                                                     in
                                                                    (uu____40846,
                                                                    [x],
                                                                    uu____40883)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____40828
                                                                    uu____40829
                                                                     in
                                                                    let uu____40948
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____40821,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____40948)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____40810
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____40965
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____41003
                                                                    =
                                                                    let uu____41010
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____41010
                                                                    dapp1  in
                                                                    [uu____41003])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____40965
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____41038
                                                                    =
                                                                    let uu____41049
                                                                    =
                                                                    let uu____41056
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____41057
                                                                    =
                                                                    let uu____41074
                                                                    =
                                                                    let uu____41075
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____41075
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____41077
                                                                    =
                                                                    let uu____41084
                                                                    =
                                                                    let uu____41095
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____41095)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____41084
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____41074,
                                                                    uu____41077)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____41056
                                                                    uu____41057
                                                                     in
                                                                    (uu____41049,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____41038)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | FStar_Syntax_Syntax.Tm_fvar
                                                         fv ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____41174 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____41174
                                                          with
                                                          | (encoded_args,arg_decls)
                                                              ->
                                                              let guards_for_parameter
                                                                orig_arg arg
                                                                xv =
                                                                let fv1 =
                                                                  match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                  with
                                                                  | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                  | uu____41273
                                                                    ->
                                                                    let uu____41274
                                                                    =
                                                                    let uu____41280
                                                                    =
                                                                    let uu____41282
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____41282
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____41280)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____41274
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____41323
                                                                    =
                                                                    let uu____41325
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____41325
                                                                     in
                                                                    if
                                                                    uu____41323
                                                                    then
                                                                    let uu____41350
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____41350]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____41368
                                                                =
                                                                let uu____41399
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____41494
                                                                     ->
                                                                    fun
                                                                    uu____41495
                                                                     ->
                                                                    match 
                                                                    (uu____41494,
                                                                    uu____41495)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____41743
                                                                    =
                                                                    let uu____41765
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____41765
                                                                     in
                                                                    (match uu____41743
                                                                    with
                                                                    | 
                                                                    (uu____41806,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____41851
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____41851
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____41869
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____41869
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                  (env', [],
                                                                    [],
                                                                    (Prims.parse_int "0"))
                                                                  uu____41399
                                                                 in
                                                              (match uu____41368
                                                               with
                                                               | (uu____41952,arg_vars,elim_eqns_or_guards,uu____41955)
                                                                   ->
                                                                   let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                   let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
                                                                    arg_vars1
                                                                     in
                                                                   let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                   let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                   let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                   let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                   let typing_inversion
                                                                    =
                                                                    let uu____42059
                                                                    =
                                                                    let uu____42070
                                                                    =
                                                                    let uu____42077
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____42078
                                                                    =
                                                                    let uu____42095
                                                                    =
                                                                    let uu____42096
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____42096
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____42098
                                                                    =
                                                                    let uu____42105
                                                                    =
                                                                    let uu____42116
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____42116)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____42105
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____42095,
                                                                    uu____42098)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____42077
                                                                    uu____42078
                                                                     in
                                                                    (uu____42070,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____42059
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____42173
                                                                    =
                                                                    let uu____42174
                                                                    =
                                                                    let uu____42180
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____42180,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____42174
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____42173
                                                                     in
                                                                    let uu____42186
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____42186
                                                                    then
                                                                    let x =
                                                                    let uu____42190
                                                                    =
                                                                    let uu____42196
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____42196,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____42190
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____42207
                                                                    =
                                                                    let uu____42218
                                                                    =
                                                                    let uu____42225
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____42226
                                                                    =
                                                                    let uu____42243
                                                                    =
                                                                    let uu____42251
                                                                    =
                                                                    let uu____42257
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____42257]
                                                                     in
                                                                    [uu____42251]
                                                                     in
                                                                    let uu____42280
                                                                    =
                                                                    let uu____42287
                                                                    =
                                                                    let uu____42298
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____42306
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____42298,
                                                                    uu____42306)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____42287
                                                                     in
                                                                    (uu____42243,
                                                                    [x],
                                                                    uu____42280)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____42225
                                                                    uu____42226
                                                                     in
                                                                    let uu____42345
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____42218,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____42345)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____42207
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____42362
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____42400
                                                                    =
                                                                    let uu____42407
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____42407
                                                                    dapp1  in
                                                                    [uu____42400])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____42362
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____42435
                                                                    =
                                                                    let uu____42446
                                                                    =
                                                                    let uu____42453
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____42454
                                                                    =
                                                                    let uu____42471
                                                                    =
                                                                    let uu____42472
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____42472
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____42474
                                                                    =
                                                                    let uu____42481
                                                                    =
                                                                    let uu____42492
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____42492)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____42481
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____42471,
                                                                    uu____42474)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____42453
                                                                    uu____42454
                                                                     in
                                                                    (uu____42446,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____42435)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____42546 ->
                                                         ((let uu____42548 =
                                                             let uu____42554
                                                               =
                                                               let uu____42556
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____42558
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____42556
                                                                 uu____42558
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____42554)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____42548);
                                                          ([], [])))
                                                 in
                                              let uu____42574 =
                                                encode_elim ()  in
                                              (match uu____42574 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____42627 =
                                                       let uu____42634 =
                                                         let uu____42641 =
                                                           let uu____42648 =
                                                             let uu____42655
                                                               =
                                                               let uu____42658
                                                                 =
                                                                 let uu____42661
                                                                   =
                                                                   let uu____42662
                                                                    =
                                                                    let uu____42674
                                                                    =
                                                                    let uu____42675
                                                                    =
                                                                    let uu____42677
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____42677
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____42675
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____42674)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____42662
                                                                    in
                                                                 [uu____42661]
                                                                  in
                                                               FStar_List.append
                                                                 uu____42658
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____42655
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____42692 =
                                                             let uu____42699
                                                               =
                                                               let uu____42706
                                                                 =
                                                                 let uu____42713
                                                                   =
                                                                   let uu____42716
                                                                    =
                                                                    let uu____42719
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____42727
                                                                    =
                                                                    let uu____42730
                                                                    =
                                                                    let uu____42731
                                                                    =
                                                                    let uu____42742
                                                                    =
                                                                    let uu____42749
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____42750
                                                                    =
                                                                    let uu____42767
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____42767)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____42749
                                                                    uu____42750
                                                                     in
                                                                    (uu____42742,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____42731
                                                                     in
                                                                    let uu____42813
                                                                    =
                                                                    let uu____42816
                                                                    =
                                                                    let uu____42817
                                                                    =
                                                                    let uu____42828
                                                                    =
                                                                    let uu____42835
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____42836
                                                                    =
                                                                    let uu____42853
                                                                    =
                                                                    let uu____42854
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____42854
                                                                    vars'  in
                                                                    let uu____42856
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____42853,
                                                                    uu____42856)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____42835
                                                                    uu____42836
                                                                     in
                                                                    (uu____42828,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____42817
                                                                     in
                                                                    [uu____42816]
                                                                     in
                                                                    uu____42730
                                                                    ::
                                                                    uu____42813
                                                                     in
                                                                    uu____42719
                                                                    ::
                                                                    uu____42727
                                                                     in
                                                                   FStar_List.append
                                                                    uu____42716
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____42713
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____42706
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____42699
                                                              in
                                                           FStar_List.append
                                                             uu____42648
                                                             uu____42692
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____42641
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____42634
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____42627
                                                      in
                                                   let uu____42934 =
                                                     let uu____42935 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____42935 g
                                                      in
                                                   (uu____42934, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____43055  ->
              fun se  ->
                match uu____43055 with
                | (g,env1) ->
                    let uu____43140 = encode_sigelt env1 se  in
                    (match uu____43140 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____43368 =
        match uu____43368 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____43480 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____43518 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____43518
                   then
                     let uu____43523 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____43525 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____43527 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____43523 uu____43525 uu____43527
                   else ());
                  (let uu____43532 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____43532 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____43574 =
                         let uu____43596 =
                           let uu____43598 =
                             let uu____43600 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____43600
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____43598  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____43596
                          in
                       (match uu____43574 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____43672 = FStar_Options.log_queries ()
                                 in
                              if uu____43672
                              then
                                let uu____43675 =
                                  let uu____43677 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____43679 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____43681 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____43677 uu____43679 uu____43681
                                   in
                                FStar_Pervasives_Native.Some uu____43675
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____43704 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____43722 =
                                let uu____43729 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____43729  in
                              FStar_List.append uu____43704 uu____43722  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____43776,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____43836 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____43836 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____43924 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____43924 with | (uu____44011,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____44105  ->
              match uu____44105 with
              | (l,uu____44114,uu____44115) ->
                  let uu____44118 =
                    let uu____44130 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____44130, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____44118))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____44163  ->
              match uu____44163 with
              | (l,uu____44174,uu____44175) ->
                  let uu____44178 =
                    let uu____44179 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _44182  -> FStar_SMTEncoding_Term.Echo _44182)
                      uu____44179
                     in
                  let uu____44183 =
                    let uu____44186 =
                      let uu____44187 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____44187  in
                    [uu____44186]  in
                  uu____44178 :: uu____44183))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____44352 =
      let uu____44366 =
        let uu____44389 = FStar_Util.psmap_empty ()  in
        let uu____44420 =
          let uu____44449 = FStar_Util.psmap_empty ()  in (uu____44449, [])
           in
        let uu____44506 =
          let uu____44508 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____44508 FStar_Ident.string_of_lid  in
        let uu____44522 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____44389;
          FStar_SMTEncoding_Env.fvar_bindings = uu____44420;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____44506;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____44522
        }  in
      [uu____44366]  in
    FStar_ST.op_Colon_Equals last_env uu____44352
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____44745 = FStar_ST.op_Bang last_env  in
      match uu____44745 with
      | [] -> failwith "No env; call init first!"
      | e::uu____44839 ->
          let uu___1540_44875 = e  in
          let uu____44898 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1540_44875.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1540_44875.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1540_44875.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1540_44875.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1540_44875.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1540_44875.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1540_44875.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____44898;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1540_44875.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1540_44875.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____44928 = FStar_ST.op_Bang last_env  in
    match uu____44928 with
    | [] -> failwith "Empty env stack"
    | uu____44999::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____45097  ->
    let uu____45098 = FStar_ST.op_Bang last_env  in
    match uu____45098 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____45301  ->
    let uu____45302 = FStar_ST.op_Bang last_env  in
    match uu____45302 with
    | [] -> failwith "Popping an empty stack"
    | uu____45373::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____45465  -> FStar_Common.snapshot push_env last_env () 
let (rollback_env : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_env last_env depth 
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (snapshot :
  Prims.string -> (FStar_TypeChecker_Env.solver_depth_t * unit)) =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____45648  ->
         let uu____45649 = snapshot_env ()  in
         match uu____45649 with
         | (env_depth,()) ->
             let uu____45671 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____45671 with
              | (varops_depth,()) ->
                  let uu____45693 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____45693 with
                   | (z3_depth,()) ->
                       ((env_depth, varops_depth, z3_depth), ()))))
  
let (rollback :
  Prims.string ->
    FStar_TypeChecker_Env.solver_depth_t FStar_Pervasives_Native.option ->
      unit)
  =
  fun msg  ->
    fun depth  ->
      FStar_Util.atomically
        (fun uu____45751  ->
           let uu____45752 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____45752 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____45847 = snapshot msg  in () 
let (pop : Prims.string -> unit) =
  fun msg  -> rollback msg FStar_Pervasives_Native.None 
let (open_fact_db_tags :
  FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  = fun env  -> [] 
let (place_decl_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____45937::uu____45938,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1601_45953 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1601_45953.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1601_45953.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1601_45953.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____45968 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1607_46033 = elt  in
        let uu____46042 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1607_46033.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1607_46033.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____46042;
          FStar_SMTEncoding_Term.a_names =
            (uu___1607_46033.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____46092 =
        let uu____46095 =
          let uu____46096 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____46096  in
        let uu____46105 = open_fact_db_tags env  in uu____46095 ::
          uu____46105
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____46092
  
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_elt Prims.list *
        FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____46187 = encode_sigelt env se  in
      match uu____46187 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_elt_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (recover_caching_and_update_env :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun decls  ->
      FStar_All.pipe_right decls
        (FStar_List.collect
           (fun elt  ->
              if
                elt.FStar_SMTEncoding_Term.key = FStar_Pervasives_Native.None
              then [elt]
              else
                (let uu____46366 =
                   let uu____46373 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____46373
                    in
                 match uu____46366 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____46412 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____46412
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____46572 = FStar_Options.log_queries ()  in
        if uu____46572
        then
          let uu____46577 =
            let uu____46578 =
              let uu____46580 =
                let uu____46582 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____46582 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____46580  in
            FStar_SMTEncoding_Term.Caption uu____46578  in
          uu____46577 :: decls
        else decls  in
      (let uu____46609 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____46609
       then
         let uu____46612 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____46612
       else ());
      (let env =
         let uu____46640 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____46640 tcenv  in
       let uu____46649 = encode_top_level_facts env se  in
       match uu____46649 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____46708 =
               let uu____46711 =
                 let uu____46714 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____46714
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____46711  in
             FStar_SMTEncoding_Z3.giveZ3 uu____46708)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____46769 = FStar_Options.log_queries ()  in
          if uu____46769
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1645_46789 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1645_46789.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1645_46789.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1645_46789.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1645_46789.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1645_46789.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1645_46789.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1645_46789.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1645_46789.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1645_46789.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1645_46789.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____46816 =
             let uu____46819 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____46819
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____46816  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____46973 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____46973
      then ([], [])
      else
        (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.reset_fresh ();
         (let name =
            FStar_Util.format2 "%s %s"
              (if modul.FStar_Syntax_Syntax.is_interface
               then "interface"
               else "module")
              (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
             in
          (let uu____47031 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____47031
           then
             let uu____47034 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____47034
           else ());
          (let env =
             let uu____47069 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____47069
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____47229  ->
                     fun se  ->
                       match uu____47229 with
                       | (g,env2) ->
                           let uu____47314 = encode_top_level_facts env2 se
                              in
                           (match uu____47314 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____47435 =
             encode_signature
               (let uu___1668_47459 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1668_47459.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1668_47459.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1668_47459.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1668_47459.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1668_47459.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1668_47459.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1668_47459.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1668_47459.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1668_47459.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1668_47459.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____47435 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____47537 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____47537
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____47543 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____47543))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____47680  ->
        match uu____47680 with
        | (decls,fvbs) ->
            ((let uu____47782 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____47782
              then ()
              else
                (let uu____47787 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____47787
                 then
                   let uu____47790 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____47790
                 else ()));
             (let env =
                let uu____47824 = get_env name tcenv  in
                FStar_All.pipe_right uu____47824
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____47892 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____47892
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____48009 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____48009
               then
                 FStar_Util.print1
                   "Done encoding externals from cache for %s\n"
                   name.FStar_Ident.str
               else ())))
  
let (encode_query :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_ErrorReporting.label Prims.list *
          FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl
          Prims.list))
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____48187 =
           let uu____48189 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____48189.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____48187);
        (let env =
           let uu____48221 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____48221 tcenv  in
         let uu____48230 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____48278 = aux rest  in
                 (match uu____48278 with
                  | (out,rest1) ->
                      let t =
                        let uu____48314 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____48314 with
                        | FStar_Pervasives_Native.Some uu____48321 ->
                            let uu____48322 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____48322
                              x.FStar_Syntax_Syntax.sort
                        | uu____48333 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding true;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____48346 =
                        let uu____48349 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1709_48352 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1709_48352.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1709_48352.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____48349 :: out  in
                      (uu____48346, rest1))
             | uu____48367 -> ([], bindings)  in
           let uu____48374 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____48374 with
           | (closing,bindings) ->
               let uu____48405 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____48405, bindings)
            in
         match uu____48230 with
         | (q1,bindings) ->
             let uu____48456 = encode_env_bindings env bindings  in
             (match uu____48456 with
              | (env_decls,env1) ->
                  ((let uu____48511 =
                      ((FStar_TypeChecker_Env.debug tcenv
                          FStar_Options.Medium)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____48511
                    then
                      let uu____48518 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____48518
                    else ());
                   (let uu____48523 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____48523 with
                    | (phi,qdecls) ->
                        let uu____48553 =
                          let uu____48561 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____48561 phi
                           in
                        (match uu____48553 with
                         | (labels,phi1) ->
                             let uu____48584 = encode_labels labels  in
                             (match uu____48584 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____48620 =
                                      FStar_Options.log_queries ()  in
                                    if uu____48620
                                    then
                                      let uu____48625 =
                                        let uu____48626 =
                                          let uu____48628 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____48628
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____48626
                                         in
                                      [uu____48625]
                                    else []  in
                                  let query_prelude =
                                    let uu____48636 =
                                      let uu____48637 =
                                        let uu____48638 =
                                          let uu____48645 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____48660 =
                                            let uu____48667 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____48667
                                             in
                                          FStar_List.append uu____48645
                                            uu____48660
                                           in
                                        FStar_List.append env_decls
                                          uu____48638
                                         in
                                      FStar_All.pipe_right uu____48637
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____48636
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____48697 =
                                      let uu____48708 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____48715 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____48708,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____48715)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____48697
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  