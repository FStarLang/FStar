open Prims
let (norm_before_encoding :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.Eager_unfolding;
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
  let uu____154 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____154 with
  | (asym,a) ->
      let uu____165 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____165 with
       | (xsym,x) ->
           let uu____176 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____176 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____254 =
                      let uu____266 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____266, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____254  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____286 =
                      let uu____294 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____294)  in
                    FStar_SMTEncoding_Util.mkApp uu____286  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____313 =
                    let uu____316 =
                      let uu____319 =
                        let uu____322 =
                          let uu____323 =
                            let uu____331 =
                              let uu____332 =
                                let uu____343 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____343)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____332
                               in
                            (uu____331, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____323  in
                        let uu____355 =
                          let uu____358 =
                            let uu____359 =
                              let uu____367 =
                                FStar_SMTEncoding_Term.mk_IsTotFun xtok1  in
                              (uu____367, FStar_Pervasives_Native.None,
                                (Prims.op_Hat "primitive_tot_fun_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____359  in
                          let uu____371 =
                            let uu____374 =
                              let uu____375 =
                                let uu____383 =
                                  let uu____384 =
                                    let uu____395 =
                                      FStar_SMTEncoding_Util.mkEq
                                        (xtok_app, xapp)
                                       in
                                    ([[xtok_app]], vars, uu____395)  in
                                  FStar_SMTEncoding_Term.mkForall rng
                                    uu____384
                                   in
                                (uu____383,
                                  (FStar_Pervasives_Native.Some
                                     "Name-token correspondence"),
                                  (Prims.op_Hat "token_correspondence_" x1))
                                 in
                              FStar_SMTEncoding_Util.mkAssume uu____375  in
                            [uu____374]  in
                          uu____358 :: uu____371  in
                        uu____322 :: uu____355  in
                      xtok_decl :: uu____319  in
                    xname_decl :: uu____316  in
                  (xtok1, (FStar_List.length vars), uu____313)  in
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
                  let uu____565 =
                    let uu____586 =
                      let uu____605 =
                        let uu____606 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____606
                         in
                      quant axy uu____605  in
                    (FStar_Parser_Const.op_Eq, uu____586)  in
                  let uu____623 =
                    let uu____646 =
                      let uu____667 =
                        let uu____686 =
                          let uu____687 =
                            let uu____688 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____688  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____687
                           in
                        quant axy uu____686  in
                      (FStar_Parser_Const.op_notEq, uu____667)  in
                    let uu____705 =
                      let uu____728 =
                        let uu____749 =
                          let uu____768 =
                            let uu____769 =
                              let uu____770 =
                                let uu____775 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____776 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____775, uu____776)  in
                              FStar_SMTEncoding_Util.mkAnd uu____770  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____769
                             in
                          quant xy uu____768  in
                        (FStar_Parser_Const.op_And, uu____749)  in
                      let uu____793 =
                        let uu____816 =
                          let uu____837 =
                            let uu____856 =
                              let uu____857 =
                                let uu____858 =
                                  let uu____863 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____864 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____863, uu____864)  in
                                FStar_SMTEncoding_Util.mkOr uu____858  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____857
                               in
                            quant xy uu____856  in
                          (FStar_Parser_Const.op_Or, uu____837)  in
                        let uu____881 =
                          let uu____904 =
                            let uu____925 =
                              let uu____944 =
                                let uu____945 =
                                  let uu____946 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____946  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____945
                                 in
                              quant qx uu____944  in
                            (FStar_Parser_Const.op_Negation, uu____925)  in
                          let uu____963 =
                            let uu____986 =
                              let uu____1007 =
                                let uu____1026 =
                                  let uu____1027 =
                                    let uu____1028 =
                                      let uu____1033 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1034 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1033, uu____1034)  in
                                    FStar_SMTEncoding_Util.mkLT uu____1028
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1027
                                   in
                                quant xy uu____1026  in
                              (FStar_Parser_Const.op_LT, uu____1007)  in
                            let uu____1051 =
                              let uu____1074 =
                                let uu____1095 =
                                  let uu____1114 =
                                    let uu____1115 =
                                      let uu____1116 =
                                        let uu____1121 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1122 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1121, uu____1122)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1116
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1115
                                     in
                                  quant xy uu____1114  in
                                (FStar_Parser_Const.op_LTE, uu____1095)  in
                              let uu____1139 =
                                let uu____1162 =
                                  let uu____1183 =
                                    let uu____1202 =
                                      let uu____1203 =
                                        let uu____1204 =
                                          let uu____1209 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1210 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1209, uu____1210)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1204
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1203
                                       in
                                    quant xy uu____1202  in
                                  (FStar_Parser_Const.op_GT, uu____1183)  in
                                let uu____1227 =
                                  let uu____1250 =
                                    let uu____1271 =
                                      let uu____1290 =
                                        let uu____1291 =
                                          let uu____1292 =
                                            let uu____1297 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1298 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1297, uu____1298)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1292
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1291
                                         in
                                      quant xy uu____1290  in
                                    (FStar_Parser_Const.op_GTE, uu____1271)
                                     in
                                  let uu____1315 =
                                    let uu____1338 =
                                      let uu____1359 =
                                        let uu____1378 =
                                          let uu____1379 =
                                            let uu____1380 =
                                              let uu____1385 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1386 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1385, uu____1386)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1380
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1379
                                           in
                                        quant xy uu____1378  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1359)
                                       in
                                    let uu____1403 =
                                      let uu____1426 =
                                        let uu____1447 =
                                          let uu____1466 =
                                            let uu____1467 =
                                              let uu____1468 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1468
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1467
                                             in
                                          quant qx uu____1466  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1447)
                                         in
                                      let uu____1485 =
                                        let uu____1508 =
                                          let uu____1529 =
                                            let uu____1548 =
                                              let uu____1549 =
                                                let uu____1550 =
                                                  let uu____1555 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1556 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1555, uu____1556)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1550
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1549
                                               in
                                            quant xy uu____1548  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1529)
                                           in
                                        let uu____1573 =
                                          let uu____1596 =
                                            let uu____1617 =
                                              let uu____1636 =
                                                let uu____1637 =
                                                  let uu____1638 =
                                                    let uu____1643 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____1644 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____1643, uu____1644)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____1638
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____1637
                                                 in
                                              quant xy uu____1636  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____1617)
                                             in
                                          let uu____1661 =
                                            let uu____1684 =
                                              let uu____1705 =
                                                let uu____1724 =
                                                  let uu____1725 =
                                                    let uu____1726 =
                                                      let uu____1731 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____1732 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____1731,
                                                        uu____1732)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____1726
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____1725
                                                   in
                                                quant xy uu____1724  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____1705)
                                               in
                                            let uu____1749 =
                                              let uu____1772 =
                                                let uu____1793 =
                                                  let uu____1812 =
                                                    let uu____1813 =
                                                      let uu____1814 =
                                                        let uu____1819 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____1820 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____1819,
                                                          uu____1820)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____1814
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____1813
                                                     in
                                                  quant xy uu____1812  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____1793)
                                                 in
                                              let uu____1837 =
                                                let uu____1860 =
                                                  let uu____1881 =
                                                    let uu____1900 =
                                                      let uu____1901 =
                                                        let uu____1902 =
                                                          let uu____1907 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____1908 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____1907,
                                                            uu____1908)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____1902
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____1901
                                                       in
                                                    quant xy uu____1900  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____1881)
                                                   in
                                                let uu____1925 =
                                                  let uu____1948 =
                                                    let uu____1969 =
                                                      let uu____1988 =
                                                        let uu____1989 =
                                                          let uu____1990 =
                                                            let uu____1995 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____1996 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____1995,
                                                              uu____1996)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____1990
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____1989
                                                         in
                                                      quant xy uu____1988  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____1969)
                                                     in
                                                  let uu____2013 =
                                                    let uu____2036 =
                                                      let uu____2057 =
                                                        let uu____2076 =
                                                          let uu____2077 =
                                                            let uu____2078 =
                                                              let uu____2083
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2084
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2083,
                                                                uu____2084)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2078
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2077
                                                           in
                                                        quant xy uu____2076
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2057)
                                                       in
                                                    let uu____2101 =
                                                      let uu____2124 =
                                                        let uu____2145 =
                                                          let uu____2164 =
                                                            let uu____2165 =
                                                              let uu____2166
                                                                =
                                                                let uu____2171
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2172
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2171,
                                                                  uu____2172)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2166
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2165
                                                             in
                                                          quant xy uu____2164
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2145)
                                                         in
                                                      let uu____2189 =
                                                        let uu____2212 =
                                                          let uu____2233 =
                                                            let uu____2252 =
                                                              let uu____2253
                                                                =
                                                                let uu____2254
                                                                  =
                                                                  let uu____2259
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2260
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2259,
                                                                    uu____2260)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2254
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2253
                                                               in
                                                            quant xy
                                                              uu____2252
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2233)
                                                           in
                                                        let uu____2277 =
                                                          let uu____2300 =
                                                            let uu____2321 =
                                                              let uu____2340
                                                                =
                                                                let uu____2341
                                                                  =
                                                                  let uu____2342
                                                                    =
                                                                    let uu____2347
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2348
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2347,
                                                                    uu____2348)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2342
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2341
                                                                 in
                                                              quant xy
                                                                uu____2340
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2321)
                                                             in
                                                          let uu____2365 =
                                                            let uu____2388 =
                                                              let uu____2409
                                                                =
                                                                let uu____2428
                                                                  =
                                                                  let uu____2429
                                                                    =
                                                                    let uu____2430
                                                                    =
                                                                    let uu____2435
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2436
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2435,
                                                                    uu____2436)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2430
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2429
                                                                   in
                                                                quant xy
                                                                  uu____2428
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2409)
                                                               in
                                                            let uu____2453 =
                                                              let uu____2476
                                                                =
                                                                let uu____2497
                                                                  =
                                                                  let uu____2516
                                                                    =
                                                                    let uu____2517
                                                                    =
                                                                    let uu____2518
                                                                    =
                                                                    let uu____2523
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2524
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2523,
                                                                    uu____2524)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2518
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2517
                                                                     in
                                                                  quant xy
                                                                    uu____2516
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2497)
                                                                 in
                                                              let uu____2541
                                                                =
                                                                let uu____2564
                                                                  =
                                                                  let uu____2585
                                                                    =
                                                                    let uu____2604
                                                                    =
                                                                    let uu____2605
                                                                    =
                                                                    let uu____2606
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____2606
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2605
                                                                     in
                                                                    quant qx
                                                                    uu____2604
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____2585)
                                                                   in
                                                                [uu____2564]
                                                                 in
                                                              uu____2476 ::
                                                                uu____2541
                                                               in
                                                            uu____2388 ::
                                                              uu____2453
                                                             in
                                                          uu____2300 ::
                                                            uu____2365
                                                           in
                                                        uu____2212 ::
                                                          uu____2277
                                                         in
                                                      uu____2124 ::
                                                        uu____2189
                                                       in
                                                    uu____2036 :: uu____2101
                                                     in
                                                  uu____1948 :: uu____2013
                                                   in
                                                uu____1860 :: uu____1925  in
                                              uu____1772 :: uu____1837  in
                                            uu____1684 :: uu____1749  in
                                          uu____1596 :: uu____1661  in
                                        uu____1508 :: uu____1573  in
                                      uu____1426 :: uu____1485  in
                                    uu____1338 :: uu____1403  in
                                  uu____1250 :: uu____1315  in
                                uu____1162 :: uu____1227  in
                              uu____1074 :: uu____1139  in
                            uu____986 :: uu____1051  in
                          uu____904 :: uu____963  in
                        uu____816 :: uu____881  in
                      uu____728 :: uu____793  in
                    uu____646 :: uu____705  in
                  uu____565 :: uu____623  in
                let mk1 l v1 =
                  let uu____3145 =
                    let uu____3157 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____3247  ->
                              match uu____3247 with
                              | (l',uu____3268) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3157
                      (FStar_Option.map
                         (fun uu____3367  ->
                            match uu____3367 with
                            | (uu____3395,b) ->
                                let uu____3429 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3429 v1))
                     in
                  FStar_All.pipe_right uu____3145 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____3512  ->
                          match uu____3512 with
                          | (l',uu____3533) -> FStar_Ident.lid_equals l l'))
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
          let uu____3607 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3607 with
          | (xxsym,xx) ->
              let uu____3618 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____3618 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____3634 =
                     let uu____3642 =
                       let uu____3643 =
                         let uu____3654 =
                           let uu____3655 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____3665 =
                             let uu____3676 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____3676 :: vars  in
                           uu____3655 :: uu____3665  in
                         let uu____3702 =
                           let uu____3703 =
                             let uu____3708 =
                               let uu____3709 =
                                 let uu____3714 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3714)  in
                               FStar_SMTEncoding_Util.mkEq uu____3709  in
                             (xx_has_type, uu____3708)  in
                           FStar_SMTEncoding_Util.mkImp uu____3703  in
                         ([[xx_has_type]], uu____3654, uu____3702)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____3643  in
                     let uu____3727 =
                       let uu____3729 =
                         let uu____3731 =
                           let uu____3733 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____3733  in
                         Prims.op_Hat module_name uu____3731  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3729
                        in
                     (uu____3642, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3727)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____3634)
  
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
    let uu____3789 =
      let uu____3791 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____3791  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3789  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3813 =
      let uu____3814 =
        let uu____3822 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3822, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3814  in
    let uu____3827 =
      let uu____3830 =
        let uu____3831 =
          let uu____3839 =
            let uu____3840 =
              let uu____3851 =
                let uu____3852 =
                  let uu____3857 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3857)  in
                FStar_SMTEncoding_Util.mkImp uu____3852  in
              ([[typing_pred]], [xx], uu____3851)  in
            let uu____3882 =
              let uu____3897 = FStar_TypeChecker_Env.get_range env  in
              let uu____3898 = mkForall_fuel1 env  in uu____3898 uu____3897
               in
            uu____3882 uu____3840  in
          (uu____3839, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3831  in
      [uu____3830]  in
    uu____3813 :: uu____3827  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3945 =
      let uu____3946 =
        let uu____3954 =
          let uu____3955 = FStar_TypeChecker_Env.get_range env  in
          let uu____3956 =
            let uu____3967 =
              let uu____3972 =
                let uu____3975 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3975]  in
              [uu____3972]  in
            let uu____3980 =
              let uu____3981 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3981 tt  in
            (uu____3967, [bb], uu____3980)  in
          FStar_SMTEncoding_Term.mkForall uu____3955 uu____3956  in
        (uu____3954, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3946  in
    let uu____4006 =
      let uu____4009 =
        let uu____4010 =
          let uu____4018 =
            let uu____4019 =
              let uu____4030 =
                let uu____4031 =
                  let uu____4036 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____4036)  in
                FStar_SMTEncoding_Util.mkImp uu____4031  in
              ([[typing_pred]], [xx], uu____4030)  in
            let uu____4063 =
              let uu____4078 = FStar_TypeChecker_Env.get_range env  in
              let uu____4079 = mkForall_fuel1 env  in uu____4079 uu____4078
               in
            uu____4063 uu____4019  in
          (uu____4018, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4010  in
      [uu____4009]  in
    uu____3945 :: uu____4006  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____4122 =
        let uu____4123 =
          let uu____4129 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4129, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4123  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4122  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4143 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4143  in
    let uu____4148 =
      let uu____4149 =
        let uu____4157 =
          let uu____4158 = FStar_TypeChecker_Env.get_range env  in
          let uu____4159 =
            let uu____4170 =
              let uu____4175 =
                let uu____4178 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4178]  in
              [uu____4175]  in
            let uu____4183 =
              let uu____4184 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4184 tt  in
            (uu____4170, [bb], uu____4183)  in
          FStar_SMTEncoding_Term.mkForall uu____4158 uu____4159  in
        (uu____4157, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4149  in
    let uu____4209 =
      let uu____4212 =
        let uu____4213 =
          let uu____4221 =
            let uu____4222 =
              let uu____4233 =
                let uu____4234 =
                  let uu____4239 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4239)  in
                FStar_SMTEncoding_Util.mkImp uu____4234  in
              ([[typing_pred]], [xx], uu____4233)  in
            let uu____4266 =
              let uu____4281 = FStar_TypeChecker_Env.get_range env  in
              let uu____4282 = mkForall_fuel1 env  in uu____4282 uu____4281
               in
            uu____4266 uu____4222  in
          (uu____4221, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4213  in
      let uu____4304 =
        let uu____4307 =
          let uu____4308 =
            let uu____4316 =
              let uu____4317 =
                let uu____4328 =
                  let uu____4329 =
                    let uu____4334 =
                      let uu____4335 =
                        let uu____4338 =
                          let uu____4341 =
                            let uu____4344 =
                              let uu____4345 =
                                let uu____4350 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4351 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____4350, uu____4351)  in
                              FStar_SMTEncoding_Util.mkGT uu____4345  in
                            let uu____4353 =
                              let uu____4356 =
                                let uu____4357 =
                                  let uu____4362 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4363 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____4362, uu____4363)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4357  in
                              let uu____4365 =
                                let uu____4368 =
                                  let uu____4369 =
                                    let uu____4374 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4375 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4374, uu____4375)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4369  in
                                [uu____4368]  in
                              uu____4356 :: uu____4365  in
                            uu____4344 :: uu____4353  in
                          typing_pred_y :: uu____4341  in
                        typing_pred :: uu____4338  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4335  in
                    (uu____4334, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4329  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4328)
                 in
              let uu____4408 =
                let uu____4423 = FStar_TypeChecker_Env.get_range env  in
                let uu____4424 = mkForall_fuel1 env  in uu____4424 uu____4423
                 in
              uu____4408 uu____4317  in
            (uu____4316,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4308  in
        [uu____4307]  in
      uu____4212 :: uu____4304  in
    uu____4148 :: uu____4209  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____4467 =
        let uu____4468 =
          let uu____4474 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4474, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4468  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4467  in
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
      let uu____4490 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4490  in
    let uu____4495 =
      let uu____4496 =
        let uu____4504 =
          let uu____4505 = FStar_TypeChecker_Env.get_range env  in
          let uu____4506 =
            let uu____4517 =
              let uu____4522 =
                let uu____4525 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4525]  in
              [uu____4522]  in
            let uu____4530 =
              let uu____4531 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4531 tt  in
            (uu____4517, [bb], uu____4530)  in
          FStar_SMTEncoding_Term.mkForall uu____4505 uu____4506  in
        (uu____4504, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4496  in
    let uu____4556 =
      let uu____4559 =
        let uu____4560 =
          let uu____4568 =
            let uu____4569 =
              let uu____4580 =
                let uu____4581 =
                  let uu____4586 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____4586)  in
                FStar_SMTEncoding_Util.mkImp uu____4581  in
              ([[typing_pred]], [xx], uu____4580)  in
            let uu____4613 =
              let uu____4628 = FStar_TypeChecker_Env.get_range env  in
              let uu____4629 = mkForall_fuel1 env  in uu____4629 uu____4628
               in
            uu____4613 uu____4569  in
          (uu____4568, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4560  in
      let uu____4651 =
        let uu____4654 =
          let uu____4655 =
            let uu____4663 =
              let uu____4664 =
                let uu____4675 =
                  let uu____4676 =
                    let uu____4681 =
                      let uu____4682 =
                        let uu____4685 =
                          let uu____4688 =
                            let uu____4691 =
                              let uu____4692 =
                                let uu____4697 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____4698 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____4697, uu____4698)  in
                              FStar_SMTEncoding_Util.mkGT uu____4692  in
                            let uu____4700 =
                              let uu____4703 =
                                let uu____4704 =
                                  let uu____4709 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____4710 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____4709, uu____4710)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4704  in
                              let uu____4712 =
                                let uu____4715 =
                                  let uu____4716 =
                                    let uu____4721 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____4722 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____4721, uu____4722)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4716  in
                                [uu____4715]  in
                              uu____4703 :: uu____4712  in
                            uu____4691 :: uu____4700  in
                          typing_pred_y :: uu____4688  in
                        typing_pred :: uu____4685  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4682  in
                    (uu____4681, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4676  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4675)
                 in
              let uu____4755 =
                let uu____4770 = FStar_TypeChecker_Env.get_range env  in
                let uu____4771 = mkForall_fuel1 env  in uu____4771 uu____4770
                 in
              uu____4755 uu____4664  in
            (uu____4663,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4655  in
        [uu____4654]  in
      uu____4559 :: uu____4651  in
    uu____4495 :: uu____4556  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4818 =
      let uu____4819 =
        let uu____4827 =
          let uu____4828 = FStar_TypeChecker_Env.get_range env  in
          let uu____4829 =
            let uu____4840 =
              let uu____4845 =
                let uu____4848 = FStar_SMTEncoding_Term.boxString b  in
                [uu____4848]  in
              [uu____4845]  in
            let uu____4853 =
              let uu____4854 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4854 tt  in
            (uu____4840, [bb], uu____4853)  in
          FStar_SMTEncoding_Term.mkForall uu____4828 uu____4829  in
        (uu____4827, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4819  in
    let uu____4879 =
      let uu____4882 =
        let uu____4883 =
          let uu____4891 =
            let uu____4892 =
              let uu____4903 =
                let uu____4904 =
                  let uu____4909 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____4909)  in
                FStar_SMTEncoding_Util.mkImp uu____4904  in
              ([[typing_pred]], [xx], uu____4903)  in
            let uu____4936 =
              let uu____4951 = FStar_TypeChecker_Env.get_range env  in
              let uu____4952 = mkForall_fuel1 env  in uu____4952 uu____4951
               in
            uu____4936 uu____4892  in
          (uu____4891, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4883  in
      [uu____4882]  in
    uu____4818 :: uu____4879  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____4999 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____4999]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____5029 =
      let uu____5030 =
        let uu____5038 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____5038, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5030  in
    [uu____5029]  in
  let mk_and_interp env conj uu____5061 =
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
    let uu____5090 =
      let uu____5091 =
        let uu____5099 =
          let uu____5100 = FStar_TypeChecker_Env.get_range env  in
          let uu____5101 =
            let uu____5112 =
              let uu____5113 =
                let uu____5118 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____5118, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5113  in
            ([[l_and_a_b]], [aa; bb], uu____5112)  in
          FStar_SMTEncoding_Term.mkForall uu____5100 uu____5101  in
        (uu____5099, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5091  in
    [uu____5090]  in
  let mk_or_interp env disj uu____5173 =
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
    let uu____5202 =
      let uu____5203 =
        let uu____5211 =
          let uu____5212 = FStar_TypeChecker_Env.get_range env  in
          let uu____5213 =
            let uu____5224 =
              let uu____5225 =
                let uu____5230 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5230, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5225  in
            ([[l_or_a_b]], [aa; bb], uu____5224)  in
          FStar_SMTEncoding_Term.mkForall uu____5212 uu____5213  in
        (uu____5211, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5203  in
    [uu____5202]  in
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
    let uu____5308 =
      let uu____5309 =
        let uu____5317 =
          let uu____5318 = FStar_TypeChecker_Env.get_range env  in
          let uu____5319 =
            let uu____5330 =
              let uu____5331 =
                let uu____5336 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5336, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5331  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5330)  in
          FStar_SMTEncoding_Term.mkForall uu____5318 uu____5319  in
        (uu____5317, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5309  in
    [uu____5308]  in
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
    let uu____5426 =
      let uu____5427 =
        let uu____5435 =
          let uu____5436 = FStar_TypeChecker_Env.get_range env  in
          let uu____5437 =
            let uu____5448 =
              let uu____5449 =
                let uu____5454 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5454, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5449  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5448)  in
          FStar_SMTEncoding_Term.mkForall uu____5436 uu____5437  in
        (uu____5435, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5427  in
    [uu____5426]  in
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
    let uu____5554 =
      let uu____5555 =
        let uu____5563 =
          let uu____5564 = FStar_TypeChecker_Env.get_range env  in
          let uu____5565 =
            let uu____5576 =
              let uu____5577 =
                let uu____5582 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____5582, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5577  in
            ([[l_imp_a_b]], [aa; bb], uu____5576)  in
          FStar_SMTEncoding_Term.mkForall uu____5564 uu____5565  in
        (uu____5563, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5555  in
    [uu____5554]  in
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
    let uu____5666 =
      let uu____5667 =
        let uu____5675 =
          let uu____5676 = FStar_TypeChecker_Env.get_range env  in
          let uu____5677 =
            let uu____5688 =
              let uu____5689 =
                let uu____5694 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____5694, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5689  in
            ([[l_iff_a_b]], [aa; bb], uu____5688)  in
          FStar_SMTEncoding_Term.mkForall uu____5676 uu____5677  in
        (uu____5675, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5667  in
    [uu____5666]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____5765 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____5765  in
    let uu____5770 =
      let uu____5771 =
        let uu____5779 =
          let uu____5780 = FStar_TypeChecker_Env.get_range env  in
          let uu____5781 =
            let uu____5792 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____5792)  in
          FStar_SMTEncoding_Term.mkForall uu____5780 uu____5781  in
        (uu____5779, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5771  in
    [uu____5770]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____5845 =
      let uu____5846 =
        let uu____5854 =
          let uu____5855 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____5855 range_ty  in
        let uu____5856 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____5854, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____5856)
         in
      FStar_SMTEncoding_Util.mkAssume uu____5846  in
    [uu____5845]  in
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
        let uu____5902 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____5902 x1 t  in
      let uu____5904 = FStar_TypeChecker_Env.get_range env  in
      let uu____5905 =
        let uu____5916 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____5916)  in
      FStar_SMTEncoding_Term.mkForall uu____5904 uu____5905  in
    let uu____5941 =
      let uu____5942 =
        let uu____5950 =
          let uu____5951 = FStar_TypeChecker_Env.get_range env  in
          let uu____5952 =
            let uu____5963 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____5963)  in
          FStar_SMTEncoding_Term.mkForall uu____5951 uu____5952  in
        (uu____5950,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5942  in
    [uu____5941]  in
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
    let uu____6024 =
      let uu____6025 =
        let uu____6033 =
          let uu____6034 = FStar_TypeChecker_Env.get_range env  in
          let uu____6035 =
            let uu____6051 =
              let uu____6052 =
                let uu____6057 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____6058 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____6057, uu____6058)  in
              FStar_SMTEncoding_Util.mkAnd uu____6052  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____6051)
             in
          FStar_SMTEncoding_Term.mkForall' uu____6034 uu____6035  in
        (uu____6033,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6025  in
    [uu____6024]  in
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
          let uu____6616 =
            FStar_Util.find_opt
              (fun uu____6654  ->
                 match uu____6654 with
                 | (l,uu____6670) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____6616 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____6713,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____6774 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____6774 with
        | (form,decls) ->
            let uu____6783 =
              let uu____6786 =
                let uu____6789 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____6789]  in
              FStar_All.pipe_right uu____6786
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____6783
  
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
              let uu____6848 =
                ((let uu____6852 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____6852) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____6848
              then
                let arg_sorts =
                  let uu____6864 =
                    let uu____6865 = FStar_Syntax_Subst.compress t_norm  in
                    uu____6865.FStar_Syntax_Syntax.n  in
                  match uu____6864 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6871) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6909  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6916 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6918 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6918 with
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
                    let uu____6950 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____6950, env1)
              else
                (let uu____6955 = prims.is lid  in
                 if uu____6955
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6964 = prims.mk lid vname  in
                   match uu____6964 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____6988 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____6988, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6997 =
                      let uu____7016 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____7016 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7044 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7044
                            then
                              let uu____7049 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___295_7052 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___295_7052.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___295_7052.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___295_7052.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___295_7052.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___295_7052.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___295_7052.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___295_7052.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___295_7052.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___295_7052.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___295_7052.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___295_7052.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___295_7052.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___295_7052.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___295_7052.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___295_7052.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___295_7052.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___295_7052.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___295_7052.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___295_7052.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___295_7052.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___295_7052.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___295_7052.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___295_7052.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___295_7052.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___295_7052.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___295_7052.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___295_7052.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___295_7052.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___295_7052.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___295_7052.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___295_7052.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___295_7052.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___295_7052.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___295_7052.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___295_7052.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___295_7052.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___295_7052.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___295_7052.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___295_7052.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___295_7052.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___295_7052.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___295_7052.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7049
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7075 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____7075)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6997 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_7181  ->
                                  match uu___0_7181 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7185 = FStar_Util.prefix vars
                                         in
                                      (match uu____7185 with
                                       | (uu____7218,xxv) ->
                                           let xx =
                                             let uu____7257 =
                                               let uu____7258 =
                                                 let uu____7264 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7264,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7258
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7257
                                              in
                                           let uu____7267 =
                                             let uu____7268 =
                                               let uu____7276 =
                                                 let uu____7277 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7278 =
                                                   let uu____7289 =
                                                     let uu____7290 =
                                                       let uu____7295 =
                                                         let uu____7296 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7296
                                                          in
                                                       (vapp, uu____7295)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7290
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7289)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7277 uu____7278
                                                  in
                                               (uu____7276,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7268
                                              in
                                           [uu____7267])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7311 = FStar_Util.prefix vars
                                         in
                                      (match uu____7311 with
                                       | (uu____7344,xxv) ->
                                           let xx =
                                             let uu____7383 =
                                               let uu____7384 =
                                                 let uu____7390 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7390,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7384
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7383
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
                                           let uu____7401 =
                                             let uu____7402 =
                                               let uu____7410 =
                                                 let uu____7411 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7412 =
                                                   let uu____7423 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7423)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7411 uu____7412
                                                  in
                                               (uu____7410,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7402
                                              in
                                           [uu____7401])
                                  | uu____7436 -> []))
                           in
                        let uu____7437 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7437 with
                         | (vars,guards,env',decls1,uu____7462) ->
                             let uu____7475 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7488 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7488, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7492 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7492 with
                                    | (g,ds) ->
                                        let uu____7505 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7505,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7475 with
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
                                  let should_thunk uu____7528 =
                                    let is_type1 t =
                                      let uu____7536 =
                                        let uu____7537 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7537.FStar_Syntax_Syntax.n  in
                                      match uu____7536 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7541 -> true
                                      | uu____7543 -> false  in
                                    let is_squash1 t =
                                      let uu____7552 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____7552 with
                                      | (head1,uu____7571) ->
                                          let uu____7596 =
                                            let uu____7597 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____7597.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7596 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____7602;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____7603;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____7605;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____7606;_};_},uu____7607)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____7615 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____7620 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____7620))
                                       &&
                                       (let uu____7626 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____7626))
                                      &&
                                      (let uu____7629 = is_type1 t_norm  in
                                       Prims.op_Negation uu____7629)
                                     in
                                  let uu____7631 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____7690 -> (false, vars)  in
                                  (match uu____7631 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____7740 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____7740 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____7772 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [])
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____7793 ->
                                                  let uu____7802 =
                                                    let uu____7810 =
                                                      get_vtok ()  in
                                                    (uu____7810, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7802
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____7817 =
                                                let uu____7825 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____7825)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____7817
                                               in
                                            let uu____7839 =
                                              let vname_decl =
                                                let uu____7847 =
                                                  let uu____7859 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____7859,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____7847
                                                 in
                                              let uu____7870 =
                                                let env2 =
                                                  let uu___390_7876 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___390_7876.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____7877 =
                                                  let uu____7879 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____7879
                                                   in
                                                if uu____7877
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____7870 with
                                              | (tok_typing,decls2) ->
                                                  let uu____7896 =
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
                                                        let uu____7922 =
                                                          let uu____7925 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____7925
                                                           in
                                                        let uu____7932 =
                                                          let uu____7933 =
                                                            let uu____7936 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (vname, [])
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _7942  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _7942)
                                                              uu____7936
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____7933
                                                           in
                                                        (uu____7922,
                                                          uu____7932)
                                                    | uu____7945 when thunked
                                                        -> (decls2, env1)
                                                    | uu____7958 ->
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
                                                          let uu____7982 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____7983 =
                                                            let uu____7994 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____7994)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____7982
                                                            uu____7983
                                                           in
                                                        let name_tok_corr =
                                                          let uu____8004 =
                                                            let uu____8012 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____8012,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8004
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
                                                            let uu____8023 =
                                                              let uu____8024
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8024]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8023
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8051 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8052 =
                                                              let uu____8063
                                                                =
                                                                let uu____8064
                                                                  =
                                                                  let uu____8069
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8070
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8069,
                                                                    uu____8070)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8064
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8063)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8051
                                                              uu____8052
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8099 =
                                                          let uu____8102 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8102
                                                           in
                                                        (uu____8099, env1)
                                                     in
                                                  (match uu____7896 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8123 =
                                                         let uu____8126 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8126
                                                           tok_decl
                                                          in
                                                       (uu____8123, env2))
                                               in
                                            (match uu____7839 with
                                             | (decls2,env2) ->
                                                 let uu____8145 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8155 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8155 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8170 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8170, decls)
                                                    in
                                                 (match uu____8145 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8185 =
                                                          let uu____8193 =
                                                            let uu____8194 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8195 =
                                                              let uu____8206
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8206)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8194
                                                              uu____8195
                                                             in
                                                          (uu____8193,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8185
                                                         in
                                                      let freshness =
                                                        let uu____8222 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8222
                                                        then
                                                          let uu____8230 =
                                                            let uu____8231 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8232 =
                                                              let uu____8245
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8252
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8245,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8252)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8231
                                                              uu____8232
                                                             in
                                                          let uu____8258 =
                                                            let uu____8261 =
                                                              let uu____8262
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8262
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8261]  in
                                                          uu____8230 ::
                                                            uu____8258
                                                        else []  in
                                                      let g =
                                                        let uu____8268 =
                                                          let uu____8271 =
                                                            let uu____8274 =
                                                              let uu____8277
                                                                =
                                                                let uu____8280
                                                                  =
                                                                  let uu____8283
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8283
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8280
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8277
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8274
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8271
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8268
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
          let uu____8323 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8323 with
          | FStar_Pervasives_Native.None  ->
              let uu____8334 = encode_free_var false env x t t_norm []  in
              (match uu____8334 with
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
            let uu____8397 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8397 with
            | (decls,env1) ->
                let uu____8408 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8408
                then
                  let uu____8415 =
                    let uu____8416 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8416  in
                  (uu____8415, env1)
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
             (fun uu____8472  ->
                fun lb  ->
                  match uu____8472 with
                  | (decls,env1) ->
                      let uu____8492 =
                        let uu____8497 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8497
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8492 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8526 = FStar_Syntax_Util.head_and_args t  in
    match uu____8526 with
    | (hd1,args) ->
        let uu____8570 =
          let uu____8571 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8571.FStar_Syntax_Syntax.n  in
        (match uu____8570 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8577,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____8601 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____8612 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___474_8620 = en  in
    let uu____8621 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___474_8620.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___474_8620.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___474_8620.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___474_8620.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___474_8620.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___474_8620.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___474_8620.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___474_8620.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___474_8620.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___474_8620.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____8621
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____8651  ->
      fun quals  ->
        match uu____8651 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8756 = FStar_Util.first_N nbinders formals  in
              match uu____8756 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____8853  ->
                         fun uu____8854  ->
                           match (uu____8853, uu____8854) with
                           | ((formal,uu____8880),(binder,uu____8882)) ->
                               let uu____8903 =
                                 let uu____8910 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____8910)  in
                               FStar_Syntax_Syntax.NT uu____8903) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____8924 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8965  ->
                              match uu____8965 with
                              | (x,i) ->
                                  let uu____8984 =
                                    let uu___500_8985 = x  in
                                    let uu____8986 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___500_8985.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___500_8985.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8986
                                    }  in
                                  (uu____8984, i)))
                       in
                    FStar_All.pipe_right uu____8924
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9010 =
                      let uu____9015 = FStar_Syntax_Subst.compress body  in
                      let uu____9016 =
                        let uu____9017 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9017
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____9015 uu____9016
                       in
                    uu____9010 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___507_9066 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___507_9066.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___507_9066.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___507_9066.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___507_9066.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___507_9066.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___507_9066.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___507_9066.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___507_9066.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___507_9066.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___507_9066.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___507_9066.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___507_9066.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___507_9066.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___507_9066.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___507_9066.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___507_9066.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___507_9066.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___507_9066.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___507_9066.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___507_9066.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___507_9066.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___507_9066.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___507_9066.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___507_9066.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___507_9066.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___507_9066.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___507_9066.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___507_9066.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___507_9066.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___507_9066.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___507_9066.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___507_9066.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___507_9066.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___507_9066.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___507_9066.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___507_9066.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___507_9066.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___507_9066.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___507_9066.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___507_9066.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___507_9066.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___507_9066.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____9138  ->
                       fun uu____9139  ->
                         match (uu____9138, uu____9139) with
                         | ((x,uu____9165),(b,uu____9167)) ->
                             let uu____9188 =
                               let uu____9195 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9195)  in
                             FStar_Syntax_Syntax.NT uu____9188) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9220 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9220
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9249 ->
                    let uu____9256 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9256
                | uu____9257 when Prims.op_Negation norm1 ->
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
                | uu____9260 ->
                    let uu____9261 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9261)
                 in
              let aux t1 e1 =
                let uu____9303 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9303 with
                | (binders,body,lopt) ->
                    let uu____9335 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9351 -> arrow_formals_comp_norm false t1  in
                    (match uu____9335 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9385 =
                           if nformals < nbinders
                           then
                             let uu____9419 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9419 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9499 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9499)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9529 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9529 with
                                | (binders1,body1) ->
                                    let uu____9582 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____9582))
                             else
                               (let uu____9595 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____9595))
                            in
                         (match uu____9385 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____9655 = aux t e  in
              match uu____9655 with
              | (binders,body,comp) ->
                  let uu____9701 =
                    let uu____9712 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____9712
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____9727 = aux comp1 body1  in
                      match uu____9727 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____9701 with
                   | (binders1,body1,comp1) ->
                       let uu____9810 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____9810, comp1))
               in
            (try
               (fun uu___577_9837  ->
                  match () with
                  | () ->
                      let uu____9844 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9844
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9860 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9923  ->
                                   fun lb  ->
                                     match uu____9923 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9978 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9978
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9984 =
                                             let uu____9993 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9993
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9984 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9860 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10134;
                                    FStar_Syntax_Syntax.lbeff = uu____10135;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10137;
                                    FStar_Syntax_Syntax.lbpos = uu____10138;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10162 =
                                     let uu____10169 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10169 with
                                     | (tcenv',uu____10185,e_t) ->
                                         let uu____10191 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10202 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10191 with
                                          | (e1,t_norm1) ->
                                              ((let uu___640_10219 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___640_10219.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10162 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10229 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10229 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10249 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10249
                                               then
                                                 let uu____10254 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10257 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10254 uu____10257
                                               else ());
                                              (let uu____10262 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10262 with
                                               | (vars,_guards,env'1,binder_decls,uu____10289)
                                                   ->
                                                   let uu____10302 =
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
                                                         let uu____10319 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10319
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10341 =
                                                          let uu____10342 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10343 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10342 fvb
                                                            uu____10343
                                                           in
                                                        (vars, uu____10341))
                                                      in
                                                   (match uu____10302 with
                                                    | (vars1,app) ->
                                                        let uu____10354 =
                                                          let is_logical =
                                                            let uu____10367 =
                                                              let uu____10368
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10368.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10367
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10374 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10378 =
                                                              let uu____10379
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10379
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10378
                                                              (fun lid  ->
                                                                 let uu____10388
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10388
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10389 =
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
                                                          if uu____10389
                                                          then
                                                            let uu____10405 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10406 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10405,
                                                              uu____10406)
                                                          else
                                                            (let uu____10417
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10417))
                                                           in
                                                        (match uu____10354
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10441
                                                                 =
                                                                 let uu____10449
                                                                   =
                                                                   let uu____10450
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10451
                                                                    =
                                                                    let uu____10462
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10462)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10450
                                                                    uu____10451
                                                                    in
                                                                 let uu____10471
                                                                   =
                                                                   let uu____10472
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10472
                                                                    in
                                                                 (uu____10449,
                                                                   uu____10471,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10441
                                                                in
                                                             let uu____10478
                                                               =
                                                               let uu____10481
                                                                 =
                                                                 let uu____10484
                                                                   =
                                                                   let uu____10487
                                                                    =
                                                                    let uu____10490
                                                                    =
                                                                    let uu____10493
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10493
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10490
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10487
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10484
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10481
                                                                in
                                                             (uu____10478,
                                                               env2)))))))
                               | uu____10502 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10562 =
                                   let uu____10568 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____10568,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10562  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10574 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10627  ->
                                         fun fvb  ->
                                           match uu____10627 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10682 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10682
                                                  in
                                               let gtok =
                                                 let uu____10686 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10686
                                                  in
                                               let env4 =
                                                 let uu____10689 =
                                                   let uu____10692 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _10698  ->
                                                        FStar_Pervasives_Native.Some
                                                          _10698) uu____10692
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10689
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10574 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10818
                                     t_norm uu____10820 =
                                     match (uu____10818, uu____10820) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10850;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10851;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10853;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10854;_})
                                         ->
                                         let uu____10881 =
                                           let uu____10888 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10888 with
                                           | (tcenv',uu____10904,e_t) ->
                                               let uu____10910 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10921 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10910 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___727_10938 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___727_10938.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10881 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10951 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10951
                                                then
                                                  let uu____10956 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10958 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10960 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10956 uu____10958
                                                    uu____10960
                                                else ());
                                               (let uu____10965 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____10965 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____10992 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____10992 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11014 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11014
                                                           then
                                                             let uu____11019
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11021
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11024
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11026
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11019
                                                               uu____11021
                                                               uu____11024
                                                               uu____11026
                                                           else ());
                                                          (let uu____11031 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11031
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11060)
                                                               ->
                                                               let uu____11073
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11086
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11086,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11090
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11090
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11103
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11103,
                                                                    decls0))
                                                                  in
                                                               (match uu____11073
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
                                                                    let uu____11124
                                                                    =
                                                                    let uu____11136
                                                                    =
                                                                    let uu____11139
                                                                    =
                                                                    let uu____11142
                                                                    =
                                                                    let uu____11145
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11145
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11142
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11139
                                                                     in
                                                                    (g,
                                                                    uu____11136,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11124
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
                                                                    let uu____11175
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11175
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
                                                                    let uu____11190
                                                                    =
                                                                    let uu____11193
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11193
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11190
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11199
                                                                    =
                                                                    let uu____11202
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11202
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11199
                                                                     in
                                                                    let uu____11207
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11207
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11223
                                                                    =
                                                                    let uu____11231
                                                                    =
                                                                    let uu____11232
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11233
                                                                    =
                                                                    let uu____11249
                                                                    =
                                                                    let uu____11250
                                                                    =
                                                                    let uu____11255
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11255)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11250
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11249)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11232
                                                                    uu____11233
                                                                     in
                                                                    let uu____11269
                                                                    =
                                                                    let uu____11270
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11270
                                                                     in
                                                                    (uu____11231,
                                                                    uu____11269,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11223
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11277
                                                                    =
                                                                    let uu____11285
                                                                    =
                                                                    let uu____11286
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11287
                                                                    =
                                                                    let uu____11298
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11298)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11286
                                                                    uu____11287
                                                                     in
                                                                    (uu____11285,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11277
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11312
                                                                    =
                                                                    let uu____11320
                                                                    =
                                                                    let uu____11321
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11322
                                                                    =
                                                                    let uu____11333
                                                                    =
                                                                    let uu____11334
                                                                    =
                                                                    let uu____11339
                                                                    =
                                                                    let uu____11340
                                                                    =
                                                                    let uu____11343
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11343
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11340
                                                                     in
                                                                    (gsapp,
                                                                    uu____11339)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11334
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11333)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11321
                                                                    uu____11322
                                                                     in
                                                                    (uu____11320,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11312
                                                                     in
                                                                    let uu____11357
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
                                                                    let uu____11369
                                                                    =
                                                                    let uu____11370
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11370
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11369
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____11372
                                                                    =
                                                                    let uu____11380
                                                                    =
                                                                    let uu____11381
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11382
                                                                    =
                                                                    let uu____11393
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11393)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11381
                                                                    uu____11382
                                                                     in
                                                                    (uu____11380,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11372
                                                                     in
                                                                    let uu____11406
                                                                    =
                                                                    let uu____11415
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11415
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11430
                                                                    =
                                                                    let uu____11433
                                                                    =
                                                                    let uu____11434
                                                                    =
                                                                    let uu____11442
                                                                    =
                                                                    let uu____11443
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11444
                                                                    =
                                                                    let uu____11455
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11455)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11443
                                                                    uu____11444
                                                                     in
                                                                    (uu____11442,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11434
                                                                     in
                                                                    [uu____11433]
                                                                     in
                                                                    (d3,
                                                                    uu____11430)
                                                                     in
                                                                    match uu____11406
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11357
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11512
                                                                    =
                                                                    let uu____11515
                                                                    =
                                                                    let uu____11518
                                                                    =
                                                                    let uu____11521
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11521
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11518
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11515
                                                                     in
                                                                    let uu____11528
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11512,
                                                                    uu____11528,
                                                                    env02))))))))))
                                      in
                                   let uu____11533 =
                                     let uu____11546 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11609  ->
                                          fun uu____11610  ->
                                            match (uu____11609, uu____11610)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11735 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11735 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11546
                                      in
                                   (match uu____11533 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11802 =
                                          let isDeclFun uu___1_11819 =
                                            match uu___1_11819 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11821 -> true
                                            | uu____11834 -> false  in
                                          let uu____11836 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11836
                                            (fun decls3  ->
                                               let uu____11866 =
                                                 FStar_List.fold_left
                                                   (fun uu____11897  ->
                                                      fun elt  ->
                                                        match uu____11897
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____11938 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____11938
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____11966
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____11966
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
                                                                    let uu___820_12004
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___820_12004.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___820_12004.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___820_12004.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____11866 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12036 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12036, elts, rest))
                                           in
                                        (match uu____11802 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12065 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12071  ->
                                        match uu___2_12071 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12074 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12082 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12082)))
                                in
                             if uu____12065
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___837_12104  ->
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
                   let uu____12143 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12143
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12162 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12162, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12218 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12218 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12224 = encode_sigelt' env se  in
      match uu____12224 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12236 =
                  let uu____12239 =
                    let uu____12240 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12240  in
                  [uu____12239]  in
                FStar_All.pipe_right uu____12236
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12245 ->
                let uu____12246 =
                  let uu____12249 =
                    let uu____12252 =
                      let uu____12253 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12253  in
                    [uu____12252]  in
                  FStar_All.pipe_right uu____12249
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12260 =
                  let uu____12263 =
                    let uu____12266 =
                      let uu____12269 =
                        let uu____12270 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12270  in
                      [uu____12269]  in
                    FStar_All.pipe_right uu____12266
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12263  in
                FStar_List.append uu____12246 uu____12260
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12284 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12284
       then
         let uu____12289 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12289
       else ());
      (let is_opaque_to_smt t =
         let uu____12301 =
           let uu____12302 = FStar_Syntax_Subst.compress t  in
           uu____12302.FStar_Syntax_Syntax.n  in
         match uu____12301 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12307)) -> s = "opaque_to_smt"
         | uu____12312 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12321 =
           let uu____12322 = FStar_Syntax_Subst.compress t  in
           uu____12322.FStar_Syntax_Syntax.n  in
         match uu____12321 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12327)) -> s = "uninterpreted_by_smt"
         | uu____12332 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12338 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12344 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12356 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12357 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12358 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12371 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12373 =
             let uu____12375 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12375  in
           if uu____12373
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12404 ->
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
                  let uu____12437 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____12437  in
                let uu____12438 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12438 with
                | (formals,uu____12458) ->
                    let arity = FStar_List.length formals  in
                    let uu____12482 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12482 with
                     | (aname,atok,env2) ->
                         let uu____12504 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____12504 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12520 =
                                  let uu____12521 =
                                    let uu____12533 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____12553  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12533,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12521
                                   in
                                [uu____12520;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____12570 =
                                let aux uu____12616 uu____12617 =
                                  match (uu____12616, uu____12617) with
                                  | ((bv,uu____12661),(env3,acc_sorts,acc))
                                      ->
                                      let uu____12693 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____12693 with
                                       | (xxsym,xx,env4) ->
                                           let uu____12716 =
                                             let uu____12719 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____12719 :: acc_sorts  in
                                           (env4, uu____12716, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____12570 with
                               | (uu____12751,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____12767 =
                                       let uu____12775 =
                                         let uu____12776 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12777 =
                                           let uu____12788 =
                                             let uu____12789 =
                                               let uu____12794 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____12794)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____12789
                                              in
                                           ([[app]], xs_sorts, uu____12788)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12776 uu____12777
                                          in
                                       (uu____12775,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12767
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____12809 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____12809
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____12812 =
                                       let uu____12820 =
                                         let uu____12821 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12822 =
                                           let uu____12833 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____12833)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12821 uu____12822
                                          in
                                       (uu____12820,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12812
                                      in
                                   let uu____12846 =
                                     let uu____12849 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____12849  in
                                   (env2, uu____12846))))
                 in
              let uu____12858 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____12858 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12884,uu____12885)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____12886 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____12886 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12908,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____12915 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_12921  ->
                       match uu___3_12921 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____12924 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____12930 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____12933 -> false))
                in
             Prims.op_Negation uu____12915  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____12943 =
                let uu____12948 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____12948 env fv t quals  in
              match uu____12943 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____12962 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____12962  in
                  let uu____12965 =
                    let uu____12966 =
                      let uu____12969 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____12969
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____12966  in
                  (uu____12965, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____12979 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____12979 with
            | (uvs,f1) ->
                let env1 =
                  let uu___974_12991 = env  in
                  let uu____12992 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___974_12991.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___974_12991.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___974_12991.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____12992;
                    FStar_SMTEncoding_Env.warn =
                      (uu___974_12991.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___974_12991.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___974_12991.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___974_12991.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___974_12991.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___974_12991.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___974_12991.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____12994 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____12994 with
                 | (f3,decls) ->
                     let g =
                       let uu____13008 =
                         let uu____13011 =
                           let uu____13012 =
                             let uu____13020 =
                               let uu____13021 =
                                 let uu____13023 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13023
                                  in
                               FStar_Pervasives_Native.Some uu____13021  in
                             let uu____13027 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13020, uu____13027)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13012  in
                         [uu____13011]  in
                       FStar_All.pipe_right uu____13008
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13036) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13050 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13072 =
                        let uu____13075 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13075.FStar_Syntax_Syntax.fv_name  in
                      uu____13072.FStar_Syntax_Syntax.v  in
                    let uu____13076 =
                      let uu____13078 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13078  in
                    if uu____13076
                    then
                      let val_decl =
                        let uu___991_13110 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___991_13110.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___991_13110.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___991_13110.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____13111 = encode_sigelt' env1 val_decl  in
                      match uu____13111 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13050 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13147,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13149;
                           FStar_Syntax_Syntax.lbtyp = uu____13150;
                           FStar_Syntax_Syntax.lbeff = uu____13151;
                           FStar_Syntax_Syntax.lbdef = uu____13152;
                           FStar_Syntax_Syntax.lbattrs = uu____13153;
                           FStar_Syntax_Syntax.lbpos = uu____13154;_}::[]),uu____13155)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13174 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____13174 with
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
                  let uu____13212 =
                    let uu____13215 =
                      let uu____13216 =
                        let uu____13224 =
                          let uu____13225 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13226 =
                            let uu____13237 =
                              let uu____13238 =
                                let uu____13243 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13243)  in
                              FStar_SMTEncoding_Util.mkEq uu____13238  in
                            ([[b2t_x]], [xx], uu____13237)  in
                          FStar_SMTEncoding_Term.mkForall uu____13225
                            uu____13226
                           in
                        (uu____13224,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13216  in
                    [uu____13215]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13212
                   in
                let uu____13281 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13281, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13284,uu____13285) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13295  ->
                   match uu___4_13295 with
                   | FStar_Syntax_Syntax.Discriminator uu____13297 -> true
                   | uu____13299 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13301,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13313 =
                      let uu____13315 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13315.FStar_Ident.idText  in
                    uu____13313 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13322  ->
                      match uu___5_13322 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13325 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13328) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13342  ->
                   match uu___6_13342 with
                   | FStar_Syntax_Syntax.Projector uu____13344 -> true
                   | uu____13350 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13354 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13354 with
            | FStar_Pervasives_Native.Some uu____13361 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1056_13363 = se  in
                  let uu____13364 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13364;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1056_13363.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1056_13363.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1056_13363.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13367) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1068_13388 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1068_13388.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1068_13388.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1068_13388.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1068_13388.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1068_13388.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13393) ->
           let uu____13402 = encode_sigelts env ses  in
           (match uu____13402 with
            | (g,env1) ->
                let uu____13413 =
                  FStar_List.fold_left
                    (fun uu____13437  ->
                       fun elt  ->
                         match uu____13437 with
                         | (g',inversions) ->
                             let uu____13465 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_13488  ->
                                       match uu___7_13488 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13490;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13491;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13492;_}
                                           -> false
                                       | uu____13499 -> true))
                                in
                             (match uu____13465 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1094_13524 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1094_13524.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1094_13524.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1094_13524.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13413 with
                 | (g',inversions) ->
                     let uu____13543 =
                       FStar_List.fold_left
                         (fun uu____13574  ->
                            fun elt  ->
                              match uu____13574 with
                              | (decls,elts,rest) ->
                                  let uu____13615 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_13624  ->
                                            match uu___8_13624 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____13626 -> true
                                            | uu____13639 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____13615
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____13662 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_13683  ->
                                               match uu___9_13683 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____13685 -> true
                                               | uu____13698 -> false))
                                        in
                                     match uu____13662 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1116_13729 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1116_13729.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1116_13729.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1116_13729.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____13543 with
                      | (decls,elts,rest) ->
                          let uu____13755 =
                            let uu____13756 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____13763 =
                              let uu____13766 =
                                let uu____13769 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____13769  in
                              FStar_List.append elts uu____13766  in
                            FStar_List.append uu____13756 uu____13763  in
                          (uu____13755, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____13780,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____13793 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____13793 with
             | (usubst,uvs) ->
                 let uu____13813 =
                   let uu____13820 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____13821 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____13822 =
                     let uu____13823 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____13823 k  in
                   (uu____13820, uu____13821, uu____13822)  in
                 (match uu____13813 with
                  | (env1,tps1,k1) ->
                      let uu____13836 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____13836 with
                       | (tps2,k2) ->
                           let uu____13844 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____13844 with
                            | (uu____13860,k3) ->
                                let uu____13882 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____13882 with
                                 | (tps3,env_tps,uu____13894,us) ->
                                     let u_k =
                                       let uu____13897 =
                                         let uu____13898 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____13899 =
                                           let uu____13904 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____13906 =
                                             let uu____13907 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____13907
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____13904 uu____13906
                                            in
                                         uu____13899
                                           FStar_Pervasives_Native.None
                                           uu____13898
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____13897 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____13925) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____13931,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____13934) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____13942,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____13949) ->
                                           let uu____13950 =
                                             let uu____13952 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13952
                                              in
                                           failwith uu____13950
                                       | (uu____13956,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____13957 =
                                             let uu____13959 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13959
                                              in
                                           failwith uu____13957
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____13963,uu____13964) ->
                                           let uu____13973 =
                                             let uu____13975 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13975
                                              in
                                           failwith uu____13973
                                       | (uu____13979,FStar_Syntax_Syntax.U_unif
                                          uu____13980) ->
                                           let uu____13989 =
                                             let uu____13991 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13991
                                              in
                                           failwith uu____13989
                                       | uu____13995 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14008 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14008 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14026 = u_leq_u_k u_tp  in
                                       if uu____14026
                                       then true
                                       else
                                         (let uu____14033 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14033 with
                                          | (formals,uu____14050) ->
                                              let uu____14071 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14071 with
                                               | (uu____14081,uu____14082,uu____14083,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14094 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14094
             then
               let uu____14099 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14099
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14119  ->
                       match uu___10_14119 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14123 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14136 = c  in
                 match uu____14136 with
                 | (name,args,uu____14141,uu____14142,uu____14143) ->
                     let uu____14154 =
                       let uu____14155 =
                         let uu____14167 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14194  ->
                                   match uu____14194 with
                                   | (uu____14203,sort,uu____14205) -> sort))
                            in
                         (name, uu____14167,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14155  in
                     [uu____14154]
               else
                 (let uu____14216 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14216 c)
                in
             let inversion_axioms tapp vars =
               let uu____14234 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14242 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14242 FStar_Option.isNone))
                  in
               if uu____14234
               then []
               else
                 (let uu____14277 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14277 with
                  | (xxsym,xx) ->
                      let uu____14290 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14329  ->
                                fun l  ->
                                  match uu____14329 with
                                  | (out,decls) ->
                                      let uu____14349 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14349 with
                                       | (uu____14360,data_t) ->
                                           let uu____14362 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14362 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14406 =
                                                    let uu____14407 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14407.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14406 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14410,indices)
                                                      -> indices
                                                  | uu____14436 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14466  ->
                                                            match uu____14466
                                                            with
                                                            | (x,uu____14474)
                                                                ->
                                                                let uu____14479
                                                                  =
                                                                  let uu____14480
                                                                    =
                                                                    let uu____14488
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14488,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14480
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14479)
                                                       env)
                                                   in
                                                let uu____14493 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14493 with
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
                                                                  let uu____14528
                                                                    =
                                                                    let uu____14533
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____14533,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____14528)
                                                             vars indices1
                                                         else []  in
                                                       let uu____14536 =
                                                         let uu____14537 =
                                                           let uu____14542 =
                                                             let uu____14543
                                                               =
                                                               let uu____14548
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____14549
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____14548,
                                                                 uu____14549)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____14543
                                                              in
                                                           (out, uu____14542)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____14537
                                                          in
                                                       (uu____14536,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14290 with
                       | (data_ax,decls) ->
                           let uu____14564 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____14564 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____14581 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____14581 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____14588 =
                                    let uu____14596 =
                                      let uu____14597 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____14598 =
                                        let uu____14609 =
                                          let uu____14610 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____14612 =
                                            let uu____14615 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____14615 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____14610 uu____14612
                                           in
                                        let uu____14617 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____14609,
                                          uu____14617)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____14597 uu____14598
                                       in
                                    let uu____14626 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____14596,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____14626)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____14588
                                   in
                                let uu____14632 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____14632)))
                in
             let uu____14639 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____14661 ->
                     let uu____14662 =
                       let uu____14669 =
                         let uu____14670 =
                           let uu____14685 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____14685)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____14670  in
                       FStar_Syntax_Syntax.mk uu____14669  in
                     uu____14662 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____14639 with
             | (formals,res) ->
                 let uu____14725 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____14725 with
                  | (vars,guards,env',binder_decls,uu____14750) ->
                      let arity = FStar_List.length vars  in
                      let uu____14764 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____14764 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____14790 =
                               let uu____14798 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____14798)  in
                             FStar_SMTEncoding_Util.mkApp uu____14790  in
                           let uu____14804 =
                             let tname_decl =
                               let uu____14814 =
                                 let uu____14815 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____14834 =
                                             let uu____14836 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____14836
                                              in
                                           let uu____14838 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____14834, uu____14838, false)))
                                    in
                                 let uu____14842 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____14815,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____14842, false)
                                  in
                               constructor_or_logic_type_decl uu____14814  in
                             let uu____14850 =
                               match vars with
                               | [] ->
                                   let uu____14863 =
                                     let uu____14864 =
                                       let uu____14867 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _14873  ->
                                            FStar_Pervasives_Native.Some
                                              _14873) uu____14867
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____14864
                                      in
                                   ([], uu____14863)
                               | uu____14876 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____14886 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____14886
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____14902 =
                                       let uu____14910 =
                                         let uu____14911 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14912 =
                                           let uu____14928 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____14928)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____14911 uu____14912
                                          in
                                       (uu____14910,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____14902
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____14850 with
                             | (tok_decls,env2) ->
                                 let uu____14955 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____14955
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____14804 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____14983 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____14983 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____15005 =
                                            let uu____15006 =
                                              let uu____15014 =
                                                let uu____15015 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15015
                                                 in
                                              (uu____15014,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15006
                                             in
                                          [uu____15005]
                                        else []  in
                                      let uu____15023 =
                                        let uu____15026 =
                                          let uu____15029 =
                                            let uu____15032 =
                                              let uu____15033 =
                                                let uu____15041 =
                                                  let uu____15042 =
                                                    FStar_Ident.range_of_lid
                                                      t
                                                     in
                                                  let uu____15043 =
                                                    let uu____15054 =
                                                      FStar_SMTEncoding_Util.mkImp
                                                        (guard, k1)
                                                       in
                                                    ([[tapp]], vars,
                                                      uu____15054)
                                                     in
                                                  FStar_SMTEncoding_Term.mkForall
                                                    uu____15042 uu____15043
                                                   in
                                                (uu____15041,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15033
                                               in
                                            [uu____15032]  in
                                          FStar_List.append karr uu____15029
                                           in
                                        FStar_All.pipe_right uu____15026
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15023
                                   in
                                let aux =
                                  let uu____15073 =
                                    let uu____15076 =
                                      inversion_axioms tapp vars  in
                                    let uu____15079 =
                                      let uu____15082 =
                                        let uu____15085 =
                                          let uu____15086 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15086 env2 tapp
                                            vars
                                           in
                                        [uu____15085]  in
                                      FStar_All.pipe_right uu____15082
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15076 uu____15079
                                     in
                                  FStar_List.append kindingAx uu____15073  in
                                let g =
                                  let uu____15094 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15094
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15102,uu____15103,uu____15104,uu____15105,uu____15106)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15114,t,uu____15116,n_tps,uu____15118) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15129 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15129 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15177 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15177 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15201 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15201 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15221 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15221 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15300 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15300,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15307 =
                                   let uu____15308 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15308, true)
                                    in
                                 let uu____15316 =
                                   let uu____15323 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15323
                                    in
                                 FStar_All.pipe_right uu____15307 uu____15316
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
                               let uu____15335 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15335 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15347::uu____15348 ->
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
                                            let uu____15397 =
                                              let uu____15398 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15398]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15397
                                             in
                                          let uu____15424 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15425 =
                                            let uu____15436 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15436)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15424 uu____15425
                                      | uu____15463 -> tok_typing  in
                                    let uu____15474 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15474 with
                                     | (vars',guards',env'',decls_formals,uu____15499)
                                         ->
                                         let uu____15512 =
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
                                         (match uu____15512 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____15542 ->
                                                    let uu____15551 =
                                                      let uu____15552 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____15552
                                                       in
                                                    [uu____15551]
                                                 in
                                              let encode_elim uu____15568 =
                                                let uu____15569 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____15569 with
                                                | (head1,args) ->
                                                    let uu____15620 =
                                                      let uu____15621 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____15621.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____15620 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____15633;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____15634;_},uu____15635)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____15641 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____15641
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
                                                                  | uu____15704
                                                                    ->
                                                                    let uu____15705
                                                                    =
                                                                    let uu____15711
                                                                    =
                                                                    let uu____15713
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15713
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15711)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15705
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15736
                                                                    =
                                                                    let uu____15738
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15738
                                                                     in
                                                                    if
                                                                    uu____15736
                                                                    then
                                                                    let uu____15760
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15760]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____15763
                                                                =
                                                                let uu____15777
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____15834
                                                                     ->
                                                                    fun
                                                                    uu____15835
                                                                     ->
                                                                    match 
                                                                    (uu____15834,
                                                                    uu____15835)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15946
                                                                    =
                                                                    let uu____15954
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15954
                                                                     in
                                                                    (match uu____15946
                                                                    with
                                                                    | 
                                                                    (uu____15968,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15979
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15979
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15984
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15984
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
                                                                  uu____15777
                                                                 in
                                                              (match uu____15763
                                                               with
                                                               | (uu____16005,arg_vars,elim_eqns_or_guards,uu____16008)
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
                                                                    let uu____16035
                                                                    =
                                                                    let uu____16043
                                                                    =
                                                                    let uu____16044
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16045
                                                                    =
                                                                    let uu____16056
                                                                    =
                                                                    let uu____16057
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16057
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16059
                                                                    =
                                                                    let uu____16060
                                                                    =
                                                                    let uu____16065
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16065)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16060
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16056,
                                                                    uu____16059)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16044
                                                                    uu____16045
                                                                     in
                                                                    (uu____16043,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16035
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16080
                                                                    =
                                                                    let uu____16081
                                                                    =
                                                                    let uu____16087
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16087,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16081
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16080
                                                                     in
                                                                    let uu____16090
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16090
                                                                    then
                                                                    let x =
                                                                    let uu____16094
                                                                    =
                                                                    let uu____16100
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16100,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16094
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16105
                                                                    =
                                                                    let uu____16113
                                                                    =
                                                                    let uu____16114
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16115
                                                                    =
                                                                    let uu____16126
                                                                    =
                                                                    let uu____16131
                                                                    =
                                                                    let uu____16134
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16134]
                                                                     in
                                                                    [uu____16131]
                                                                     in
                                                                    let uu____16139
                                                                    =
                                                                    let uu____16140
                                                                    =
                                                                    let uu____16145
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16147
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16145,
                                                                    uu____16147)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16140
                                                                     in
                                                                    (uu____16126,
                                                                    [x],
                                                                    uu____16139)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16114
                                                                    uu____16115
                                                                     in
                                                                    let uu____16168
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16113,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16168)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16105
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16179
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
                                                                    (let uu____16202
                                                                    =
                                                                    let uu____16203
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16203
                                                                    dapp1  in
                                                                    [uu____16202])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16179
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16210
                                                                    =
                                                                    let uu____16218
                                                                    =
                                                                    let uu____16219
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16220
                                                                    =
                                                                    let uu____16231
                                                                    =
                                                                    let uu____16232
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16232
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16234
                                                                    =
                                                                    let uu____16235
                                                                    =
                                                                    let uu____16240
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16240)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16235
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16231,
                                                                    uu____16234)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16219
                                                                    uu____16220
                                                                     in
                                                                    (uu____16218,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16210)
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
                                                         let uu____16259 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16259
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
                                                                  | uu____16322
                                                                    ->
                                                                    let uu____16323
                                                                    =
                                                                    let uu____16329
                                                                    =
                                                                    let uu____16331
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16331
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16329)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16323
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16354
                                                                    =
                                                                    let uu____16356
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16356
                                                                     in
                                                                    if
                                                                    uu____16354
                                                                    then
                                                                    let uu____16378
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16378]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16381
                                                                =
                                                                let uu____16395
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16452
                                                                     ->
                                                                    fun
                                                                    uu____16453
                                                                     ->
                                                                    match 
                                                                    (uu____16452,
                                                                    uu____16453)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16564
                                                                    =
                                                                    let uu____16572
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16572
                                                                     in
                                                                    (match uu____16564
                                                                    with
                                                                    | 
                                                                    (uu____16586,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16597
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16597
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16602
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16602
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
                                                                  uu____16395
                                                                 in
                                                              (match uu____16381
                                                               with
                                                               | (uu____16623,arg_vars,elim_eqns_or_guards,uu____16626)
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
                                                                    let uu____16653
                                                                    =
                                                                    let uu____16661
                                                                    =
                                                                    let uu____16662
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16663
                                                                    =
                                                                    let uu____16674
                                                                    =
                                                                    let uu____16675
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16675
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16677
                                                                    =
                                                                    let uu____16678
                                                                    =
                                                                    let uu____16683
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16683)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16678
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16674,
                                                                    uu____16677)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16662
                                                                    uu____16663
                                                                     in
                                                                    (uu____16661,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16653
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16698
                                                                    =
                                                                    let uu____16699
                                                                    =
                                                                    let uu____16705
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16705,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16699
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16698
                                                                     in
                                                                    let uu____16708
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16708
                                                                    then
                                                                    let x =
                                                                    let uu____16712
                                                                    =
                                                                    let uu____16718
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16718,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16712
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16723
                                                                    =
                                                                    let uu____16731
                                                                    =
                                                                    let uu____16732
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16733
                                                                    =
                                                                    let uu____16744
                                                                    =
                                                                    let uu____16749
                                                                    =
                                                                    let uu____16752
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16752]
                                                                     in
                                                                    [uu____16749]
                                                                     in
                                                                    let uu____16757
                                                                    =
                                                                    let uu____16758
                                                                    =
                                                                    let uu____16763
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16765
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16763,
                                                                    uu____16765)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16758
                                                                     in
                                                                    (uu____16744,
                                                                    [x],
                                                                    uu____16757)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16732
                                                                    uu____16733
                                                                     in
                                                                    let uu____16786
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16731,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16786)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16723
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16797
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
                                                                    (let uu____16820
                                                                    =
                                                                    let uu____16821
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16821
                                                                    dapp1  in
                                                                    [uu____16820])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16797
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16828
                                                                    =
                                                                    let uu____16836
                                                                    =
                                                                    let uu____16837
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16838
                                                                    =
                                                                    let uu____16849
                                                                    =
                                                                    let uu____16850
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16850
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16852
                                                                    =
                                                                    let uu____16853
                                                                    =
                                                                    let uu____16858
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16858)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16853
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16849,
                                                                    uu____16852)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16837
                                                                    uu____16838
                                                                     in
                                                                    (uu____16836,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16828)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____16875 ->
                                                         ((let uu____16877 =
                                                             let uu____16883
                                                               =
                                                               let uu____16885
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____16887
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____16885
                                                                 uu____16887
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____16883)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____16877);
                                                          ([], [])))
                                                 in
                                              let uu____16895 =
                                                encode_elim ()  in
                                              (match uu____16895 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____16921 =
                                                       let uu____16924 =
                                                         let uu____16927 =
                                                           let uu____16930 =
                                                             let uu____16933
                                                               =
                                                               let uu____16936
                                                                 =
                                                                 let uu____16939
                                                                   =
                                                                   let uu____16940
                                                                    =
                                                                    let uu____16952
                                                                    =
                                                                    let uu____16953
                                                                    =
                                                                    let uu____16955
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16955
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____16953
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____16952)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____16940
                                                                    in
                                                                 [uu____16939]
                                                                  in
                                                               FStar_List.append
                                                                 uu____16936
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____16933
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____16966 =
                                                             let uu____16969
                                                               =
                                                               let uu____16972
                                                                 =
                                                                 let uu____16975
                                                                   =
                                                                   let uu____16978
                                                                    =
                                                                    let uu____16981
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____16986
                                                                    =
                                                                    let uu____16989
                                                                    =
                                                                    let uu____16990
                                                                    =
                                                                    let uu____16998
                                                                    =
                                                                    let uu____16999
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17000
                                                                    =
                                                                    let uu____17011
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____17011)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16999
                                                                    uu____17000
                                                                     in
                                                                    (uu____16998,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16990
                                                                     in
                                                                    let uu____17024
                                                                    =
                                                                    let uu____17027
                                                                    =
                                                                    let uu____17028
                                                                    =
                                                                    let uu____17036
                                                                    =
                                                                    let uu____17037
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17038
                                                                    =
                                                                    let uu____17049
                                                                    =
                                                                    let uu____17050
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17050
                                                                    vars'  in
                                                                    let uu____17052
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17049,
                                                                    uu____17052)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17037
                                                                    uu____17038
                                                                     in
                                                                    (uu____17036,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17028
                                                                     in
                                                                    [uu____17027]
                                                                     in
                                                                    uu____16989
                                                                    ::
                                                                    uu____17024
                                                                     in
                                                                    uu____16981
                                                                    ::
                                                                    uu____16986
                                                                     in
                                                                   FStar_List.append
                                                                    uu____16978
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____16975
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____16972
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____16969
                                                              in
                                                           FStar_List.append
                                                             uu____16930
                                                             uu____16966
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____16927
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____16924
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____16921
                                                      in
                                                   let uu____17069 =
                                                     let uu____17070 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17070 g
                                                      in
                                                   (uu____17069, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17104  ->
              fun se  ->
                match uu____17104 with
                | (g,env1) ->
                    let uu____17124 = encode_sigelt env1 se  in
                    (match uu____17124 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17192 =
        match uu____17192 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17229 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17237 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17237
                   then
                     let uu____17242 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17244 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17246 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17242 uu____17244 uu____17246
                   else ());
                  (let uu____17251 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17251 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17269 =
                         let uu____17277 =
                           let uu____17279 =
                             let uu____17281 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17281
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17279  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17277
                          in
                       (match uu____17269 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17301 = FStar_Options.log_queries ()
                                 in
                              if uu____17301
                              then
                                let uu____17304 =
                                  let uu____17306 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17308 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17310 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17306 uu____17308 uu____17310
                                   in
                                FStar_Pervasives_Native.Some uu____17304
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17326 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17336 =
                                let uu____17339 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17339  in
                              FStar_List.append uu____17326 uu____17336  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17351,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17371 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17371 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____17392 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____17392 with | (uu____17419,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17472  ->
              match uu____17472 with
              | (l,uu____17481,uu____17482) ->
                  let uu____17485 =
                    let uu____17497 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17497, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17485))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17530  ->
              match uu____17530 with
              | (l,uu____17541,uu____17542) ->
                  let uu____17545 =
                    let uu____17546 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _17549  -> FStar_SMTEncoding_Term.Echo _17549)
                      uu____17546
                     in
                  let uu____17550 =
                    let uu____17553 =
                      let uu____17554 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17554  in
                    [uu____17553]  in
                  uu____17545 :: uu____17550))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17572 =
      let uu____17575 =
        let uu____17576 = FStar_Util.psmap_empty ()  in
        let uu____17591 =
          let uu____17600 = FStar_Util.psmap_empty ()  in (uu____17600, [])
           in
        let uu____17607 =
          let uu____17609 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____17609 FStar_Ident.string_of_lid  in
        let uu____17611 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17576;
          FStar_SMTEncoding_Env.fvar_bindings = uu____17591;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____17607;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____17611
        }  in
      [uu____17575]  in
    FStar_ST.op_Colon_Equals last_env uu____17572
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____17655 = FStar_ST.op_Bang last_env  in
      match uu____17655 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17683 ->
          let uu___1540_17686 = e  in
          let uu____17687 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1540_17686.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1540_17686.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1540_17686.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1540_17686.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1540_17686.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1540_17686.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1540_17686.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____17687;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1540_17686.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1540_17686.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____17695 = FStar_ST.op_Bang last_env  in
    match uu____17695 with
    | [] -> failwith "Empty env stack"
    | uu____17722::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____17754  ->
    let uu____17755 = FStar_ST.op_Bang last_env  in
    match uu____17755 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____17815  ->
    let uu____17816 = FStar_ST.op_Bang last_env  in
    match uu____17816 with
    | [] -> failwith "Popping an empty stack"
    | uu____17843::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____17880  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____17933  ->
         let uu____17934 = snapshot_env ()  in
         match uu____17934 with
         | (env_depth,()) ->
             let uu____17956 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____17956 with
              | (varops_depth,()) ->
                  let uu____17978 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____17978 with
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
        (fun uu____18036  ->
           let uu____18037 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18037 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18132 = snapshot msg  in () 
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
        | (uu____18178::uu____18179,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1601_18187 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1601_18187.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1601_18187.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1601_18187.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18188 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1607_18215 = elt  in
        let uu____18216 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1607_18215.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1607_18215.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18216;
          FStar_SMTEncoding_Term.a_names =
            (uu___1607_18215.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18236 =
        let uu____18239 =
          let uu____18240 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18240  in
        let uu____18241 = open_fact_db_tags env  in uu____18239 ::
          uu____18241
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18236
  
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
      let uu____18268 = encode_sigelt env se  in
      match uu____18268 with
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
                (let uu____18314 =
                   let uu____18317 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18317
                    in
                 match uu____18314 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18332 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18332
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18362 = FStar_Options.log_queries ()  in
        if uu____18362
        then
          let uu____18367 =
            let uu____18368 =
              let uu____18370 =
                let uu____18372 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18372 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18370  in
            FStar_SMTEncoding_Term.Caption uu____18368  in
          uu____18367 :: decls
        else decls  in
      (let uu____18391 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18391
       then
         let uu____18394 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18394
       else ());
      (let env =
         let uu____18400 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18400 tcenv  in
       let uu____18401 = encode_top_level_facts env se  in
       match uu____18401 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18415 =
               let uu____18418 =
                 let uu____18421 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18421
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18418  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18415)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18454 = FStar_Options.log_queries ()  in
          if uu____18454
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1645_18474 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1645_18474.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1645_18474.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1645_18474.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1645_18474.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1645_18474.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1645_18474.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1645_18474.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1645_18474.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1645_18474.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1645_18474.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18479 =
             let uu____18482 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18482
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18479  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18502 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18502
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
          (let uu____18526 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____18526
           then
             let uu____18529 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____18529
           else ());
          (let env =
             let uu____18537 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____18537
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____18576  ->
                     fun se  ->
                       match uu____18576 with
                       | (g,env2) ->
                           let uu____18596 = encode_top_level_facts env2 se
                              in
                           (match uu____18596 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____18619 =
             encode_signature
               (let uu___1668_18628 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1668_18628.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1668_18628.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1668_18628.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1668_18628.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1668_18628.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1668_18628.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1668_18628.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1668_18628.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1668_18628.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1668_18628.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____18619 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____18644 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18644
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____18650 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____18650))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____18678  ->
        match uu____18678 with
        | (decls,fvbs) ->
            ((let uu____18692 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____18692
              then ()
              else
                (let uu____18697 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18697
                 then
                   let uu____18700 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____18700
                 else ()));
             (let env =
                let uu____18708 = get_env name tcenv  in
                FStar_All.pipe_right uu____18708
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____18710 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____18710
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____18724 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____18724
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
        (let uu____18786 =
           let uu____18788 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____18788.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____18786);
        (let env =
           let uu____18790 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____18790 tcenv  in
         let uu____18791 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____18830 = aux rest  in
                 (match uu____18830 with
                  | (out,rest1) ->
                      let t =
                        let uu____18858 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____18858 with
                        | FStar_Pervasives_Native.Some uu____18861 ->
                            let uu____18862 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____18862
                              x.FStar_Syntax_Syntax.sort
                        | uu____18863 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____18867 =
                        let uu____18870 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1709_18873 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1709_18873.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1709_18873.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____18870 :: out  in
                      (uu____18867, rest1))
             | uu____18878 -> ([], bindings)  in
           let uu____18885 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____18885 with
           | (closing,bindings) ->
               let uu____18912 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____18912, bindings)
            in
         match uu____18791 with
         | (q1,bindings) ->
             let uu____18943 = encode_env_bindings env bindings  in
             (match uu____18943 with
              | (env_decls,env1) ->
                  ((let uu____18965 =
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
                    if uu____18965
                    then
                      let uu____18972 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____18972
                    else ());
                   (let uu____18977 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____18977 with
                    | (phi,qdecls) ->
                        let uu____18998 =
                          let uu____19003 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19003 phi
                           in
                        (match uu____18998 with
                         | (labels,phi1) ->
                             let uu____19020 = encode_labels labels  in
                             (match uu____19020 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19056 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19056
                                    then
                                      let uu____19061 =
                                        let uu____19062 =
                                          let uu____19064 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____19064
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19062
                                         in
                                      [uu____19061]
                                    else []  in
                                  let query_prelude =
                                    let uu____19072 =
                                      let uu____19073 =
                                        let uu____19074 =
                                          let uu____19077 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19084 =
                                            let uu____19087 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19087
                                             in
                                          FStar_List.append uu____19077
                                            uu____19084
                                           in
                                        FStar_List.append env_decls
                                          uu____19074
                                         in
                                      FStar_All.pipe_right uu____19073
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19072
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19097 =
                                      let uu____19105 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19106 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19105,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19106)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19097
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
  