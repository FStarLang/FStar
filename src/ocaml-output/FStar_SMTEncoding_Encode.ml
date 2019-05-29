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
                                let uu____368 =
                                  let uu____379 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____379)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____368
                                 in
                              (uu____367,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____359  in
                          [uu____358]  in
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
                  let uu____549 =
                    let uu____570 =
                      let uu____589 =
                        let uu____590 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____590
                         in
                      quant axy uu____589  in
                    (FStar_Parser_Const.op_Eq, uu____570)  in
                  let uu____607 =
                    let uu____630 =
                      let uu____651 =
                        let uu____670 =
                          let uu____671 =
                            let uu____672 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____672  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____671
                           in
                        quant axy uu____670  in
                      (FStar_Parser_Const.op_notEq, uu____651)  in
                    let uu____689 =
                      let uu____712 =
                        let uu____733 =
                          let uu____752 =
                            let uu____753 =
                              let uu____754 =
                                let uu____759 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____760 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____759, uu____760)  in
                              FStar_SMTEncoding_Util.mkAnd uu____754  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____753
                             in
                          quant xy uu____752  in
                        (FStar_Parser_Const.op_And, uu____733)  in
                      let uu____777 =
                        let uu____800 =
                          let uu____821 =
                            let uu____840 =
                              let uu____841 =
                                let uu____842 =
                                  let uu____847 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____848 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____847, uu____848)  in
                                FStar_SMTEncoding_Util.mkOr uu____842  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____841
                               in
                            quant xy uu____840  in
                          (FStar_Parser_Const.op_Or, uu____821)  in
                        let uu____865 =
                          let uu____888 =
                            let uu____909 =
                              let uu____928 =
                                let uu____929 =
                                  let uu____930 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____930  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____929
                                 in
                              quant qx uu____928  in
                            (FStar_Parser_Const.op_Negation, uu____909)  in
                          let uu____947 =
                            let uu____970 =
                              let uu____991 =
                                let uu____1010 =
                                  let uu____1011 =
                                    let uu____1012 =
                                      let uu____1017 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1018 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1017, uu____1018)  in
                                    FStar_SMTEncoding_Util.mkLT uu____1012
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1011
                                   in
                                quant xy uu____1010  in
                              (FStar_Parser_Const.op_LT, uu____991)  in
                            let uu____1035 =
                              let uu____1058 =
                                let uu____1079 =
                                  let uu____1098 =
                                    let uu____1099 =
                                      let uu____1100 =
                                        let uu____1105 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1106 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1105, uu____1106)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1100
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1099
                                     in
                                  quant xy uu____1098  in
                                (FStar_Parser_Const.op_LTE, uu____1079)  in
                              let uu____1123 =
                                let uu____1146 =
                                  let uu____1167 =
                                    let uu____1186 =
                                      let uu____1187 =
                                        let uu____1188 =
                                          let uu____1193 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1194 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1193, uu____1194)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1188
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1187
                                       in
                                    quant xy uu____1186  in
                                  (FStar_Parser_Const.op_GT, uu____1167)  in
                                let uu____1211 =
                                  let uu____1234 =
                                    let uu____1255 =
                                      let uu____1274 =
                                        let uu____1275 =
                                          let uu____1276 =
                                            let uu____1281 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1282 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1281, uu____1282)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1276
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1275
                                         in
                                      quant xy uu____1274  in
                                    (FStar_Parser_Const.op_GTE, uu____1255)
                                     in
                                  let uu____1299 =
                                    let uu____1322 =
                                      let uu____1343 =
                                        let uu____1362 =
                                          let uu____1363 =
                                            let uu____1364 =
                                              let uu____1369 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1370 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1369, uu____1370)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1364
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1363
                                           in
                                        quant xy uu____1362  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1343)
                                       in
                                    let uu____1387 =
                                      let uu____1410 =
                                        let uu____1431 =
                                          let uu____1450 =
                                            let uu____1451 =
                                              let uu____1452 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1452
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1451
                                             in
                                          quant qx uu____1450  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1431)
                                         in
                                      let uu____1469 =
                                        let uu____1492 =
                                          let uu____1513 =
                                            let uu____1532 =
                                              let uu____1533 =
                                                let uu____1534 =
                                                  let uu____1539 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1540 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1539, uu____1540)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1534
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1533
                                               in
                                            quant xy uu____1532  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1513)
                                           in
                                        let uu____1557 =
                                          let uu____1580 =
                                            let uu____1601 =
                                              let uu____1620 =
                                                let uu____1621 =
                                                  let uu____1622 =
                                                    let uu____1627 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____1628 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____1627, uu____1628)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____1622
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____1621
                                                 in
                                              quant xy uu____1620  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____1601)
                                             in
                                          let uu____1645 =
                                            let uu____1668 =
                                              let uu____1689 =
                                                let uu____1708 =
                                                  let uu____1709 =
                                                    let uu____1710 =
                                                      let uu____1715 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____1716 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____1715,
                                                        uu____1716)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____1710
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____1709
                                                   in
                                                quant xy uu____1708  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____1689)
                                               in
                                            let uu____1733 =
                                              let uu____1756 =
                                                let uu____1777 =
                                                  let uu____1796 =
                                                    let uu____1797 =
                                                      let uu____1798 =
                                                        let uu____1803 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____1804 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____1803,
                                                          uu____1804)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____1798
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____1797
                                                     in
                                                  quant xy uu____1796  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____1777)
                                                 in
                                              let uu____1821 =
                                                let uu____1844 =
                                                  let uu____1865 =
                                                    let uu____1884 =
                                                      let uu____1885 =
                                                        let uu____1886 =
                                                          let uu____1891 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____1892 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____1891,
                                                            uu____1892)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____1886
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____1885
                                                       in
                                                    quant xy uu____1884  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____1865)
                                                   in
                                                let uu____1909 =
                                                  let uu____1932 =
                                                    let uu____1953 =
                                                      let uu____1972 =
                                                        let uu____1973 =
                                                          let uu____1974 =
                                                            let uu____1979 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____1980 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____1979,
                                                              uu____1980)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____1974
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____1973
                                                         in
                                                      quant xy uu____1972  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____1953)
                                                     in
                                                  let uu____1997 =
                                                    let uu____2020 =
                                                      let uu____2041 =
                                                        let uu____2060 =
                                                          let uu____2061 =
                                                            let uu____2062 =
                                                              let uu____2067
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2068
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2067,
                                                                uu____2068)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2062
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2061
                                                           in
                                                        quant xy uu____2060
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2041)
                                                       in
                                                    let uu____2085 =
                                                      let uu____2108 =
                                                        let uu____2129 =
                                                          let uu____2148 =
                                                            let uu____2149 =
                                                              let uu____2150
                                                                =
                                                                let uu____2155
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2156
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2155,
                                                                  uu____2156)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2150
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2149
                                                             in
                                                          quant xy uu____2148
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2129)
                                                         in
                                                      let uu____2173 =
                                                        let uu____2196 =
                                                          let uu____2217 =
                                                            let uu____2236 =
                                                              let uu____2237
                                                                =
                                                                let uu____2238
                                                                  =
                                                                  let uu____2243
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2244
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2243,
                                                                    uu____2244)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2238
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2237
                                                               in
                                                            quant xy
                                                              uu____2236
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2217)
                                                           in
                                                        let uu____2261 =
                                                          let uu____2284 =
                                                            let uu____2305 =
                                                              let uu____2324
                                                                =
                                                                let uu____2325
                                                                  =
                                                                  let uu____2326
                                                                    =
                                                                    let uu____2331
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2332
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2331,
                                                                    uu____2332)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2326
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2325
                                                                 in
                                                              quant xy
                                                                uu____2324
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2305)
                                                             in
                                                          let uu____2349 =
                                                            let uu____2372 =
                                                              let uu____2393
                                                                =
                                                                let uu____2412
                                                                  =
                                                                  let uu____2413
                                                                    =
                                                                    let uu____2414
                                                                    =
                                                                    let uu____2419
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2420
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2419,
                                                                    uu____2420)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2414
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2413
                                                                   in
                                                                quant xy
                                                                  uu____2412
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2393)
                                                               in
                                                            let uu____2437 =
                                                              let uu____2460
                                                                =
                                                                let uu____2481
                                                                  =
                                                                  let uu____2500
                                                                    =
                                                                    let uu____2501
                                                                    =
                                                                    let uu____2502
                                                                    =
                                                                    let uu____2507
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2508
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2507,
                                                                    uu____2508)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2502
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2501
                                                                     in
                                                                  quant xy
                                                                    uu____2500
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2481)
                                                                 in
                                                              let uu____2525
                                                                =
                                                                let uu____2548
                                                                  =
                                                                  let uu____2569
                                                                    =
                                                                    let uu____2588
                                                                    =
                                                                    let uu____2589
                                                                    =
                                                                    let uu____2590
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____2590
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2589
                                                                     in
                                                                    quant qx
                                                                    uu____2588
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____2569)
                                                                   in
                                                                [uu____2548]
                                                                 in
                                                              uu____2460 ::
                                                                uu____2525
                                                               in
                                                            uu____2372 ::
                                                              uu____2437
                                                             in
                                                          uu____2284 ::
                                                            uu____2349
                                                           in
                                                        uu____2196 ::
                                                          uu____2261
                                                         in
                                                      uu____2108 ::
                                                        uu____2173
                                                       in
                                                    uu____2020 :: uu____2085
                                                     in
                                                  uu____1932 :: uu____1997
                                                   in
                                                uu____1844 :: uu____1909  in
                                              uu____1756 :: uu____1821  in
                                            uu____1668 :: uu____1733  in
                                          uu____1580 :: uu____1645  in
                                        uu____1492 :: uu____1557  in
                                      uu____1410 :: uu____1469  in
                                    uu____1322 :: uu____1387  in
                                  uu____1234 :: uu____1299  in
                                uu____1146 :: uu____1211  in
                              uu____1058 :: uu____1123  in
                            uu____970 :: uu____1035  in
                          uu____888 :: uu____947  in
                        uu____800 :: uu____865  in
                      uu____712 :: uu____777  in
                    uu____630 :: uu____689  in
                  uu____549 :: uu____607  in
                let mk1 l v1 =
                  let uu____3129 =
                    let uu____3141 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____3231  ->
                              match uu____3231 with
                              | (l',uu____3252) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3141
                      (FStar_Option.map
                         (fun uu____3351  ->
                            match uu____3351 with
                            | (uu____3379,b) ->
                                let uu____3413 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3413 v1))
                     in
                  FStar_All.pipe_right uu____3129 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____3496  ->
                          match uu____3496 with
                          | (l',uu____3517) -> FStar_Ident.lid_equals l l'))
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
          let uu____3591 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3591 with
          | (xxsym,xx) ->
              let uu____3602 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____3602 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____3618 =
                     let uu____3626 =
                       let uu____3627 =
                         let uu____3638 =
                           let uu____3639 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____3649 =
                             let uu____3660 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____3660 :: vars  in
                           uu____3639 :: uu____3649  in
                         let uu____3686 =
                           let uu____3687 =
                             let uu____3692 =
                               let uu____3693 =
                                 let uu____3698 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3698)  in
                               FStar_SMTEncoding_Util.mkEq uu____3693  in
                             (xx_has_type, uu____3692)  in
                           FStar_SMTEncoding_Util.mkImp uu____3687  in
                         ([[xx_has_type]], uu____3638, uu____3686)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____3627  in
                     let uu____3711 =
                       let uu____3713 =
                         let uu____3715 =
                           let uu____3717 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____3717  in
                         Prims.op_Hat module_name uu____3715  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3713
                        in
                     (uu____3626, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3711)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____3618)
  
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
    let uu____3773 =
      let uu____3775 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____3775  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3773  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3797 =
      let uu____3798 =
        let uu____3806 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3806, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3798  in
    let uu____3811 =
      let uu____3814 =
        let uu____3815 =
          let uu____3823 =
            let uu____3824 =
              let uu____3835 =
                let uu____3836 =
                  let uu____3841 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3841)  in
                FStar_SMTEncoding_Util.mkImp uu____3836  in
              ([[typing_pred]], [xx], uu____3835)  in
            let uu____3866 =
              let uu____3881 = FStar_TypeChecker_Env.get_range env  in
              let uu____3882 = mkForall_fuel1 env  in uu____3882 uu____3881
               in
            uu____3866 uu____3824  in
          (uu____3823, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3815  in
      [uu____3814]  in
    uu____3797 :: uu____3811  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3929 =
      let uu____3930 =
        let uu____3938 =
          let uu____3939 = FStar_TypeChecker_Env.get_range env  in
          let uu____3940 =
            let uu____3951 =
              let uu____3956 =
                let uu____3959 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3959]  in
              [uu____3956]  in
            let uu____3964 =
              let uu____3965 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3965 tt  in
            (uu____3951, [bb], uu____3964)  in
          FStar_SMTEncoding_Term.mkForall uu____3939 uu____3940  in
        (uu____3938, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3930  in
    let uu____3990 =
      let uu____3993 =
        let uu____3994 =
          let uu____4002 =
            let uu____4003 =
              let uu____4014 =
                let uu____4015 =
                  let uu____4020 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____4020)  in
                FStar_SMTEncoding_Util.mkImp uu____4015  in
              ([[typing_pred]], [xx], uu____4014)  in
            let uu____4047 =
              let uu____4062 = FStar_TypeChecker_Env.get_range env  in
              let uu____4063 = mkForall_fuel1 env  in uu____4063 uu____4062
               in
            uu____4047 uu____4003  in
          (uu____4002, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3994  in
      [uu____3993]  in
    uu____3929 :: uu____3990  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____4106 =
        let uu____4107 =
          let uu____4113 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4113, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4107  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4106  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4127 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4127  in
    let uu____4132 =
      let uu____4133 =
        let uu____4141 =
          let uu____4142 = FStar_TypeChecker_Env.get_range env  in
          let uu____4143 =
            let uu____4154 =
              let uu____4159 =
                let uu____4162 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4162]  in
              [uu____4159]  in
            let uu____4167 =
              let uu____4168 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4168 tt  in
            (uu____4154, [bb], uu____4167)  in
          FStar_SMTEncoding_Term.mkForall uu____4142 uu____4143  in
        (uu____4141, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4133  in
    let uu____4193 =
      let uu____4196 =
        let uu____4197 =
          let uu____4205 =
            let uu____4206 =
              let uu____4217 =
                let uu____4218 =
                  let uu____4223 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4223)  in
                FStar_SMTEncoding_Util.mkImp uu____4218  in
              ([[typing_pred]], [xx], uu____4217)  in
            let uu____4250 =
              let uu____4265 = FStar_TypeChecker_Env.get_range env  in
              let uu____4266 = mkForall_fuel1 env  in uu____4266 uu____4265
               in
            uu____4250 uu____4206  in
          (uu____4205, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4197  in
      let uu____4288 =
        let uu____4291 =
          let uu____4292 =
            let uu____4300 =
              let uu____4301 =
                let uu____4312 =
                  let uu____4313 =
                    let uu____4318 =
                      let uu____4319 =
                        let uu____4322 =
                          let uu____4325 =
                            let uu____4328 =
                              let uu____4329 =
                                let uu____4334 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4335 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____4334, uu____4335)  in
                              FStar_SMTEncoding_Util.mkGT uu____4329  in
                            let uu____4337 =
                              let uu____4340 =
                                let uu____4341 =
                                  let uu____4346 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4347 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____4346, uu____4347)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4341  in
                              let uu____4349 =
                                let uu____4352 =
                                  let uu____4353 =
                                    let uu____4358 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4359 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4358, uu____4359)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4353  in
                                [uu____4352]  in
                              uu____4340 :: uu____4349  in
                            uu____4328 :: uu____4337  in
                          typing_pred_y :: uu____4325  in
                        typing_pred :: uu____4322  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4319  in
                    (uu____4318, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4313  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4312)
                 in
              let uu____4392 =
                let uu____4407 = FStar_TypeChecker_Env.get_range env  in
                let uu____4408 = mkForall_fuel1 env  in uu____4408 uu____4407
                 in
              uu____4392 uu____4301  in
            (uu____4300,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4292  in
        [uu____4291]  in
      uu____4196 :: uu____4288  in
    uu____4132 :: uu____4193  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____4451 =
        let uu____4452 =
          let uu____4458 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4458, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4452  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4451  in
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
      let uu____4474 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4474  in
    let uu____4479 =
      let uu____4480 =
        let uu____4488 =
          let uu____4489 = FStar_TypeChecker_Env.get_range env  in
          let uu____4490 =
            let uu____4501 =
              let uu____4506 =
                let uu____4509 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4509]  in
              [uu____4506]  in
            let uu____4514 =
              let uu____4515 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4515 tt  in
            (uu____4501, [bb], uu____4514)  in
          FStar_SMTEncoding_Term.mkForall uu____4489 uu____4490  in
        (uu____4488, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4480  in
    let uu____4540 =
      let uu____4543 =
        let uu____4544 =
          let uu____4552 =
            let uu____4553 =
              let uu____4564 =
                let uu____4565 =
                  let uu____4570 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____4570)  in
                FStar_SMTEncoding_Util.mkImp uu____4565  in
              ([[typing_pred]], [xx], uu____4564)  in
            let uu____4597 =
              let uu____4612 = FStar_TypeChecker_Env.get_range env  in
              let uu____4613 = mkForall_fuel1 env  in uu____4613 uu____4612
               in
            uu____4597 uu____4553  in
          (uu____4552, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4544  in
      let uu____4635 =
        let uu____4638 =
          let uu____4639 =
            let uu____4647 =
              let uu____4648 =
                let uu____4659 =
                  let uu____4660 =
                    let uu____4665 =
                      let uu____4666 =
                        let uu____4669 =
                          let uu____4672 =
                            let uu____4675 =
                              let uu____4676 =
                                let uu____4681 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____4682 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____4681, uu____4682)  in
                              FStar_SMTEncoding_Util.mkGT uu____4676  in
                            let uu____4684 =
                              let uu____4687 =
                                let uu____4688 =
                                  let uu____4693 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____4694 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____4693, uu____4694)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4688  in
                              let uu____4696 =
                                let uu____4699 =
                                  let uu____4700 =
                                    let uu____4705 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____4706 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____4705, uu____4706)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4700  in
                                [uu____4699]  in
                              uu____4687 :: uu____4696  in
                            uu____4675 :: uu____4684  in
                          typing_pred_y :: uu____4672  in
                        typing_pred :: uu____4669  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4666  in
                    (uu____4665, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4660  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4659)
                 in
              let uu____4739 =
                let uu____4754 = FStar_TypeChecker_Env.get_range env  in
                let uu____4755 = mkForall_fuel1 env  in uu____4755 uu____4754
                 in
              uu____4739 uu____4648  in
            (uu____4647,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4639  in
        [uu____4638]  in
      uu____4543 :: uu____4635  in
    uu____4479 :: uu____4540  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4802 =
      let uu____4803 =
        let uu____4811 =
          let uu____4812 = FStar_TypeChecker_Env.get_range env  in
          let uu____4813 =
            let uu____4824 =
              let uu____4829 =
                let uu____4832 = FStar_SMTEncoding_Term.boxString b  in
                [uu____4832]  in
              [uu____4829]  in
            let uu____4837 =
              let uu____4838 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4838 tt  in
            (uu____4824, [bb], uu____4837)  in
          FStar_SMTEncoding_Term.mkForall uu____4812 uu____4813  in
        (uu____4811, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4803  in
    let uu____4863 =
      let uu____4866 =
        let uu____4867 =
          let uu____4875 =
            let uu____4876 =
              let uu____4887 =
                let uu____4888 =
                  let uu____4893 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____4893)  in
                FStar_SMTEncoding_Util.mkImp uu____4888  in
              ([[typing_pred]], [xx], uu____4887)  in
            let uu____4920 =
              let uu____4935 = FStar_TypeChecker_Env.get_range env  in
              let uu____4936 = mkForall_fuel1 env  in uu____4936 uu____4935
               in
            uu____4920 uu____4876  in
          (uu____4875, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4867  in
      [uu____4866]  in
    uu____4802 :: uu____4863  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____4983 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____4983]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____5013 =
      let uu____5014 =
        let uu____5022 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____5022, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5014  in
    [uu____5013]  in
  let mk_and_interp env conj uu____5045 =
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
    let uu____5074 =
      let uu____5075 =
        let uu____5083 =
          let uu____5084 = FStar_TypeChecker_Env.get_range env  in
          let uu____5085 =
            let uu____5096 =
              let uu____5097 =
                let uu____5102 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____5102, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5097  in
            ([[l_and_a_b]], [aa; bb], uu____5096)  in
          FStar_SMTEncoding_Term.mkForall uu____5084 uu____5085  in
        (uu____5083, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5075  in
    [uu____5074]  in
  let mk_or_interp env disj uu____5157 =
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
    let uu____5186 =
      let uu____5187 =
        let uu____5195 =
          let uu____5196 = FStar_TypeChecker_Env.get_range env  in
          let uu____5197 =
            let uu____5208 =
              let uu____5209 =
                let uu____5214 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5214, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5209  in
            ([[l_or_a_b]], [aa; bb], uu____5208)  in
          FStar_SMTEncoding_Term.mkForall uu____5196 uu____5197  in
        (uu____5195, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5187  in
    [uu____5186]  in
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
    let uu____5292 =
      let uu____5293 =
        let uu____5301 =
          let uu____5302 = FStar_TypeChecker_Env.get_range env  in
          let uu____5303 =
            let uu____5314 =
              let uu____5315 =
                let uu____5320 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5320, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5315  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5314)  in
          FStar_SMTEncoding_Term.mkForall uu____5302 uu____5303  in
        (uu____5301, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5293  in
    [uu____5292]  in
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
    let uu____5410 =
      let uu____5411 =
        let uu____5419 =
          let uu____5420 = FStar_TypeChecker_Env.get_range env  in
          let uu____5421 =
            let uu____5432 =
              let uu____5433 =
                let uu____5438 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5438, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5433  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5432)  in
          FStar_SMTEncoding_Term.mkForall uu____5420 uu____5421  in
        (uu____5419, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5411  in
    [uu____5410]  in
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
    let uu____5538 =
      let uu____5539 =
        let uu____5547 =
          let uu____5548 = FStar_TypeChecker_Env.get_range env  in
          let uu____5549 =
            let uu____5560 =
              let uu____5561 =
                let uu____5566 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____5566, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5561  in
            ([[l_imp_a_b]], [aa; bb], uu____5560)  in
          FStar_SMTEncoding_Term.mkForall uu____5548 uu____5549  in
        (uu____5547, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5539  in
    [uu____5538]  in
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
    let uu____5650 =
      let uu____5651 =
        let uu____5659 =
          let uu____5660 = FStar_TypeChecker_Env.get_range env  in
          let uu____5661 =
            let uu____5672 =
              let uu____5673 =
                let uu____5678 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____5678, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5673  in
            ([[l_iff_a_b]], [aa; bb], uu____5672)  in
          FStar_SMTEncoding_Term.mkForall uu____5660 uu____5661  in
        (uu____5659, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5651  in
    [uu____5650]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____5749 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____5749  in
    let uu____5754 =
      let uu____5755 =
        let uu____5763 =
          let uu____5764 = FStar_TypeChecker_Env.get_range env  in
          let uu____5765 =
            let uu____5776 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____5776)  in
          FStar_SMTEncoding_Term.mkForall uu____5764 uu____5765  in
        (uu____5763, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5755  in
    [uu____5754]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____5829 =
      let uu____5830 =
        let uu____5838 =
          let uu____5839 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____5839 range_ty  in
        let uu____5840 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____5838, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____5840)
         in
      FStar_SMTEncoding_Util.mkAssume uu____5830  in
    [uu____5829]  in
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
        let uu____5886 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____5886 x1 t  in
      let uu____5888 = FStar_TypeChecker_Env.get_range env  in
      let uu____5889 =
        let uu____5900 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____5900)  in
      FStar_SMTEncoding_Term.mkForall uu____5888 uu____5889  in
    let uu____5925 =
      let uu____5926 =
        let uu____5934 =
          let uu____5935 = FStar_TypeChecker_Env.get_range env  in
          let uu____5936 =
            let uu____5947 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____5947)  in
          FStar_SMTEncoding_Term.mkForall uu____5935 uu____5936  in
        (uu____5934,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5926  in
    [uu____5925]  in
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
    let uu____6008 =
      let uu____6009 =
        let uu____6017 =
          let uu____6018 = FStar_TypeChecker_Env.get_range env  in
          let uu____6019 =
            let uu____6035 =
              let uu____6036 =
                let uu____6041 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____6042 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____6041, uu____6042)  in
              FStar_SMTEncoding_Util.mkAnd uu____6036  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____6035)
             in
          FStar_SMTEncoding_Term.mkForall' uu____6018 uu____6019  in
        (uu____6017,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6009  in
    [uu____6008]  in
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
          let uu____6600 =
            FStar_Util.find_opt
              (fun uu____6638  ->
                 match uu____6638 with
                 | (l,uu____6654) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____6600 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____6697,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____6758 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____6758 with
        | (form,decls) ->
            let uu____6767 =
              let uu____6770 =
                let uu____6773 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____6773]  in
              FStar_All.pipe_right uu____6770
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____6767
  
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
              let uu____6832 =
                ((let uu____6836 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____6836) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____6832
              then
                let arg_sorts =
                  let uu____6848 =
                    let uu____6849 = FStar_Syntax_Subst.compress t_norm  in
                    uu____6849.FStar_Syntax_Syntax.n  in
                  match uu____6848 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6855) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6893  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6900 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6902 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6902 with
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
                    let uu____6934 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____6934, env1)
              else
                (let uu____6939 = prims.is lid  in
                 if uu____6939
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6948 = prims.mk lid vname  in
                   match uu____6948 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____6972 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____6972, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6981 =
                      let uu____7000 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____7000 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7028 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7028
                            then
                              let uu____7033 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___295_7036 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___295_7036.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___295_7036.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___295_7036.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___295_7036.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___295_7036.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___295_7036.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___295_7036.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___295_7036.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___295_7036.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___295_7036.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___295_7036.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___295_7036.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___295_7036.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___295_7036.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___295_7036.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___295_7036.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___295_7036.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___295_7036.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___295_7036.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___295_7036.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___295_7036.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___295_7036.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___295_7036.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___295_7036.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___295_7036.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___295_7036.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___295_7036.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___295_7036.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___295_7036.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___295_7036.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___295_7036.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___295_7036.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___295_7036.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___295_7036.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___295_7036.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___295_7036.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___295_7036.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___295_7036.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___295_7036.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___295_7036.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___295_7036.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___295_7036.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7033
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7059 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____7059)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6981 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_7165  ->
                                  match uu___0_7165 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7169 = FStar_Util.prefix vars
                                         in
                                      (match uu____7169 with
                                       | (uu____7202,xxv) ->
                                           let xx =
                                             let uu____7241 =
                                               let uu____7242 =
                                                 let uu____7248 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7248,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7242
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7241
                                              in
                                           let uu____7251 =
                                             let uu____7252 =
                                               let uu____7260 =
                                                 let uu____7261 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7262 =
                                                   let uu____7273 =
                                                     let uu____7274 =
                                                       let uu____7279 =
                                                         let uu____7280 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7280
                                                          in
                                                       (vapp, uu____7279)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7274
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7273)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7261 uu____7262
                                                  in
                                               (uu____7260,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7252
                                              in
                                           [uu____7251])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7295 = FStar_Util.prefix vars
                                         in
                                      (match uu____7295 with
                                       | (uu____7328,xxv) ->
                                           let xx =
                                             let uu____7367 =
                                               let uu____7368 =
                                                 let uu____7374 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7374,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7368
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7367
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
                                           let uu____7385 =
                                             let uu____7386 =
                                               let uu____7394 =
                                                 let uu____7395 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7396 =
                                                   let uu____7407 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7407)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7395 uu____7396
                                                  in
                                               (uu____7394,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7386
                                              in
                                           [uu____7385])
                                  | uu____7420 -> []))
                           in
                        let uu____7421 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7421 with
                         | (vars,guards,env',decls1,uu____7446) ->
                             let uu____7459 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7472 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7472, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7476 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7476 with
                                    | (g,ds) ->
                                        let uu____7489 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7489,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7459 with
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
                                  let should_thunk uu____7512 =
                                    let is_type1 t =
                                      let uu____7520 =
                                        let uu____7521 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7521.FStar_Syntax_Syntax.n  in
                                      match uu____7520 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7525 -> true
                                      | uu____7527 -> false  in
                                    let is_squash1 t =
                                      let uu____7536 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____7536 with
                                      | (head1,uu____7555) ->
                                          let uu____7580 =
                                            let uu____7581 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____7581.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7580 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____7586;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____7587;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____7589;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____7590;_};_},uu____7591)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____7599 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____7604 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____7604))
                                       &&
                                       (let uu____7610 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____7610))
                                      &&
                                      (let uu____7613 = is_type1 t_norm  in
                                       Prims.op_Negation uu____7613)
                                     in
                                  let uu____7615 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____7674 -> (false, vars)  in
                                  (match uu____7615 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____7724 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____7724 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____7756 =
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
                                              | uu____7777 ->
                                                  let uu____7786 =
                                                    let uu____7794 =
                                                      get_vtok ()  in
                                                    (uu____7794, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7786
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____7801 =
                                                let uu____7809 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____7809)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____7801
                                               in
                                            let uu____7823 =
                                              let vname_decl =
                                                let uu____7831 =
                                                  let uu____7843 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____7843,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____7831
                                                 in
                                              let uu____7854 =
                                                let env2 =
                                                  let uu___390_7860 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___390_7860.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____7861 =
                                                  let uu____7863 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____7863
                                                   in
                                                if uu____7861
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____7854 with
                                              | (tok_typing,decls2) ->
                                                  let uu____7880 =
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
                                                        let uu____7906 =
                                                          let uu____7909 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____7909
                                                           in
                                                        let uu____7916 =
                                                          let uu____7917 =
                                                            let uu____7920 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (vname, [])
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _7926  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _7926)
                                                              uu____7920
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____7917
                                                           in
                                                        (uu____7906,
                                                          uu____7916)
                                                    | uu____7929 when thunked
                                                        -> (decls2, env1)
                                                    | uu____7942 ->
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
                                                          let uu____7966 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____7967 =
                                                            let uu____7978 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____7978)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____7966
                                                            uu____7967
                                                           in
                                                        let name_tok_corr =
                                                          let uu____7988 =
                                                            let uu____7996 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____7996,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7988
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
                                                            let uu____8007 =
                                                              let uu____8008
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8008]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8007
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8035 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8036 =
                                                              let uu____8047
                                                                =
                                                                let uu____8048
                                                                  =
                                                                  let uu____8053
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8054
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8053,
                                                                    uu____8054)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8048
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8047)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8035
                                                              uu____8036
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8083 =
                                                          let uu____8086 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8086
                                                           in
                                                        (uu____8083, env1)
                                                     in
                                                  (match uu____7880 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8107 =
                                                         let uu____8110 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8110
                                                           tok_decl
                                                          in
                                                       (uu____8107, env2))
                                               in
                                            (match uu____7823 with
                                             | (decls2,env2) ->
                                                 let uu____8129 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8139 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8139 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8154 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8154, decls)
                                                    in
                                                 (match uu____8129 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8169 =
                                                          let uu____8177 =
                                                            let uu____8178 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8179 =
                                                              let uu____8190
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8190)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8178
                                                              uu____8179
                                                             in
                                                          (uu____8177,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8169
                                                         in
                                                      let freshness =
                                                        let uu____8206 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8206
                                                        then
                                                          let uu____8214 =
                                                            let uu____8215 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8216 =
                                                              let uu____8229
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8236
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8229,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8236)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8215
                                                              uu____8216
                                                             in
                                                          let uu____8242 =
                                                            let uu____8245 =
                                                              let uu____8246
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8246
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8245]  in
                                                          uu____8214 ::
                                                            uu____8242
                                                        else []  in
                                                      let g =
                                                        let uu____8252 =
                                                          let uu____8255 =
                                                            let uu____8258 =
                                                              let uu____8261
                                                                =
                                                                let uu____8264
                                                                  =
                                                                  let uu____8267
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8267
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8264
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8261
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8258
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8255
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8252
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
          let uu____8307 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8307 with
          | FStar_Pervasives_Native.None  ->
              let uu____8318 = encode_free_var false env x t t_norm []  in
              (match uu____8318 with
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
            let uu____8381 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8381 with
            | (decls,env1) ->
                let uu____8392 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8392
                then
                  let uu____8399 =
                    let uu____8400 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8400  in
                  (uu____8399, env1)
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
             (fun uu____8456  ->
                fun lb  ->
                  match uu____8456 with
                  | (decls,env1) ->
                      let uu____8476 =
                        let uu____8481 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8481
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8476 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8510 = FStar_Syntax_Util.head_and_args t  in
    match uu____8510 with
    | (hd1,args) ->
        let uu____8554 =
          let uu____8555 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8555.FStar_Syntax_Syntax.n  in
        (match uu____8554 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8561,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____8585 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____8596 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___474_8604 = en  in
    let uu____8605 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___474_8604.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___474_8604.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___474_8604.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___474_8604.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___474_8604.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___474_8604.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___474_8604.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___474_8604.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___474_8604.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___474_8604.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____8605
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____8635  ->
      fun quals  ->
        match uu____8635 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8740 = FStar_Util.first_N nbinders formals  in
              match uu____8740 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____8837  ->
                         fun uu____8838  ->
                           match (uu____8837, uu____8838) with
                           | ((formal,uu____8864),(binder,uu____8866)) ->
                               let uu____8887 =
                                 let uu____8894 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____8894)  in
                               FStar_Syntax_Syntax.NT uu____8887) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____8908 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8949  ->
                              match uu____8949 with
                              | (x,i) ->
                                  let uu____8968 =
                                    let uu___500_8969 = x  in
                                    let uu____8970 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___500_8969.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___500_8969.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8970
                                    }  in
                                  (uu____8968, i)))
                       in
                    FStar_All.pipe_right uu____8908
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____8994 =
                      let uu____8999 = FStar_Syntax_Subst.compress body  in
                      let uu____9000 =
                        let uu____9001 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9001
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____8999 uu____9000
                       in
                    uu____8994 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___507_9050 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___507_9050.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___507_9050.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___507_9050.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___507_9050.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___507_9050.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___507_9050.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___507_9050.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___507_9050.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___507_9050.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___507_9050.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___507_9050.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___507_9050.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___507_9050.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___507_9050.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___507_9050.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___507_9050.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___507_9050.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___507_9050.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___507_9050.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___507_9050.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___507_9050.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___507_9050.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___507_9050.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___507_9050.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___507_9050.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___507_9050.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___507_9050.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___507_9050.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___507_9050.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___507_9050.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___507_9050.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___507_9050.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___507_9050.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___507_9050.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___507_9050.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___507_9050.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___507_9050.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___507_9050.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___507_9050.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___507_9050.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___507_9050.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___507_9050.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____9122  ->
                       fun uu____9123  ->
                         match (uu____9122, uu____9123) with
                         | ((x,uu____9149),(b,uu____9151)) ->
                             let uu____9172 =
                               let uu____9179 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9179)  in
                             FStar_Syntax_Syntax.NT uu____9172) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9204 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9204
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9233 ->
                    let uu____9240 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9240
                | uu____9241 when Prims.op_Negation norm1 ->
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
                | uu____9244 ->
                    let uu____9245 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9245)
                 in
              let aux t1 e1 =
                let uu____9287 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9287 with
                | (binders,body,lopt) ->
                    let uu____9319 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9335 -> arrow_formals_comp_norm false t1  in
                    (match uu____9319 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9369 =
                           if nformals < nbinders
                           then
                             let uu____9403 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9403 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9483 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9483)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9513 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9513 with
                                | (binders1,body1) ->
                                    let uu____9566 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____9566))
                             else
                               (let uu____9579 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____9579))
                            in
                         (match uu____9369 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____9639 = aux t e  in
              match uu____9639 with
              | (binders,body,comp) ->
                  let uu____9685 =
                    let uu____9696 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____9696
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____9711 = aux comp1 body1  in
                      match uu____9711 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____9685 with
                   | (binders1,body1,comp1) ->
                       let uu____9794 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____9794, comp1))
               in
            (try
               (fun uu___577_9821  ->
                  match () with
                  | () ->
                      let uu____9828 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9828
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9844 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9907  ->
                                   fun lb  ->
                                     match uu____9907 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9962 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9962
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9968 =
                                             let uu____9977 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9977
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9968 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9844 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10118;
                                    FStar_Syntax_Syntax.lbeff = uu____10119;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10121;
                                    FStar_Syntax_Syntax.lbpos = uu____10122;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10146 =
                                     let uu____10153 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10153 with
                                     | (tcenv',uu____10169,e_t) ->
                                         let uu____10175 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10186 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10175 with
                                          | (e1,t_norm1) ->
                                              ((let uu___640_10203 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___640_10203.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10146 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10213 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10213 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10233 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10233
                                               then
                                                 let uu____10238 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10241 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10238 uu____10241
                                               else ());
                                              (let uu____10246 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10246 with
                                               | (vars,_guards,env'1,binder_decls,uu____10273)
                                                   ->
                                                   let uu____10286 =
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
                                                         let uu____10303 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10303
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10325 =
                                                          let uu____10326 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10327 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10326 fvb
                                                            uu____10327
                                                           in
                                                        (vars, uu____10325))
                                                      in
                                                   (match uu____10286 with
                                                    | (vars1,app) ->
                                                        let uu____10338 =
                                                          let is_logical =
                                                            let uu____10351 =
                                                              let uu____10352
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10352.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10351
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10358 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10362 =
                                                              let uu____10363
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10363
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10362
                                                              (fun lid  ->
                                                                 let uu____10372
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10372
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10373 =
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
                                                          if uu____10373
                                                          then
                                                            let uu____10389 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10390 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10389,
                                                              uu____10390)
                                                          else
                                                            (let uu____10401
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10401))
                                                           in
                                                        (match uu____10338
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10425
                                                                 =
                                                                 let uu____10433
                                                                   =
                                                                   let uu____10434
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10435
                                                                    =
                                                                    let uu____10446
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10446)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10434
                                                                    uu____10435
                                                                    in
                                                                 let uu____10455
                                                                   =
                                                                   let uu____10456
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10456
                                                                    in
                                                                 (uu____10433,
                                                                   uu____10455,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10425
                                                                in
                                                             let uu____10462
                                                               =
                                                               let uu____10465
                                                                 =
                                                                 let uu____10468
                                                                   =
                                                                   let uu____10471
                                                                    =
                                                                    let uu____10474
                                                                    =
                                                                    let uu____10477
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10477
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10474
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10471
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10468
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10465
                                                                in
                                                             (uu____10462,
                                                               env2)))))))
                               | uu____10486 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10546 =
                                   let uu____10552 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____10552,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10546  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10558 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10611  ->
                                         fun fvb  ->
                                           match uu____10611 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10666 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10666
                                                  in
                                               let gtok =
                                                 let uu____10670 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10670
                                                  in
                                               let env4 =
                                                 let uu____10673 =
                                                   let uu____10676 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _10682  ->
                                                        FStar_Pervasives_Native.Some
                                                          _10682) uu____10676
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10673
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10558 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10802
                                     t_norm uu____10804 =
                                     match (uu____10802, uu____10804) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10834;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10835;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10837;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10838;_})
                                         ->
                                         let uu____10865 =
                                           let uu____10872 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10872 with
                                           | (tcenv',uu____10888,e_t) ->
                                               let uu____10894 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10905 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10894 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___727_10922 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___727_10922.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10865 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10935 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10935
                                                then
                                                  let uu____10940 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10942 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10944 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10940 uu____10942
                                                    uu____10944
                                                else ());
                                               (let uu____10949 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____10949 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____10976 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____10976 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____10998 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____10998
                                                           then
                                                             let uu____11003
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11005
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11008
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11010
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11003
                                                               uu____11005
                                                               uu____11008
                                                               uu____11010
                                                           else ());
                                                          (let uu____11015 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11015
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11044)
                                                               ->
                                                               let uu____11057
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11070
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11070,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11074
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11074
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11087
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11087,
                                                                    decls0))
                                                                  in
                                                               (match uu____11057
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
                                                                    let uu____11108
                                                                    =
                                                                    let uu____11120
                                                                    =
                                                                    let uu____11123
                                                                    =
                                                                    let uu____11126
                                                                    =
                                                                    let uu____11129
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11129
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11126
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11123
                                                                     in
                                                                    (g,
                                                                    uu____11120,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11108
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
                                                                    let uu____11159
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11159
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
                                                                    let uu____11174
                                                                    =
                                                                    let uu____11177
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11177
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11174
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11183
                                                                    =
                                                                    let uu____11186
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11186
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11183
                                                                     in
                                                                    let uu____11191
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11191
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11207
                                                                    =
                                                                    let uu____11215
                                                                    =
                                                                    let uu____11216
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11217
                                                                    =
                                                                    let uu____11233
                                                                    =
                                                                    let uu____11234
                                                                    =
                                                                    let uu____11239
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11239)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11234
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11233)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11216
                                                                    uu____11217
                                                                     in
                                                                    let uu____11253
                                                                    =
                                                                    let uu____11254
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11254
                                                                     in
                                                                    (uu____11215,
                                                                    uu____11253,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11207
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11261
                                                                    =
                                                                    let uu____11269
                                                                    =
                                                                    let uu____11270
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11271
                                                                    =
                                                                    let uu____11282
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11282)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11270
                                                                    uu____11271
                                                                     in
                                                                    (uu____11269,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11261
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11296
                                                                    =
                                                                    let uu____11304
                                                                    =
                                                                    let uu____11305
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11306
                                                                    =
                                                                    let uu____11317
                                                                    =
                                                                    let uu____11318
                                                                    =
                                                                    let uu____11323
                                                                    =
                                                                    let uu____11324
                                                                    =
                                                                    let uu____11327
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11327
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11324
                                                                     in
                                                                    (gsapp,
                                                                    uu____11323)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11318
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11317)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11305
                                                                    uu____11306
                                                                     in
                                                                    (uu____11304,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11296
                                                                     in
                                                                    let uu____11341
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
                                                                    let uu____11353
                                                                    =
                                                                    let uu____11354
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11354
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11353
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____11356
                                                                    =
                                                                    let uu____11364
                                                                    =
                                                                    let uu____11365
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11366
                                                                    =
                                                                    let uu____11377
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11377)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11365
                                                                    uu____11366
                                                                     in
                                                                    (uu____11364,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11356
                                                                     in
                                                                    let uu____11390
                                                                    =
                                                                    let uu____11399
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11399
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11414
                                                                    =
                                                                    let uu____11417
                                                                    =
                                                                    let uu____11418
                                                                    =
                                                                    let uu____11426
                                                                    =
                                                                    let uu____11427
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11428
                                                                    =
                                                                    let uu____11439
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11439)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11427
                                                                    uu____11428
                                                                     in
                                                                    (uu____11426,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11418
                                                                     in
                                                                    [uu____11417]
                                                                     in
                                                                    (d3,
                                                                    uu____11414)
                                                                     in
                                                                    match uu____11390
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11341
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11496
                                                                    =
                                                                    let uu____11499
                                                                    =
                                                                    let uu____11502
                                                                    =
                                                                    let uu____11505
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11505
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11502
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11499
                                                                     in
                                                                    let uu____11512
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11496,
                                                                    uu____11512,
                                                                    env02))))))))))
                                      in
                                   let uu____11517 =
                                     let uu____11530 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11593  ->
                                          fun uu____11594  ->
                                            match (uu____11593, uu____11594)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11719 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11719 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11530
                                      in
                                   (match uu____11517 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11786 =
                                          let isDeclFun uu___1_11803 =
                                            match uu___1_11803 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11805 -> true
                                            | uu____11818 -> false  in
                                          let uu____11820 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11820
                                            (fun decls3  ->
                                               let uu____11850 =
                                                 FStar_List.fold_left
                                                   (fun uu____11881  ->
                                                      fun elt  ->
                                                        match uu____11881
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____11922 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____11922
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____11950
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____11950
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
                                                                    let uu___820_11988
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___820_11988.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___820_11988.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___820_11988.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____11850 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12020 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12020, elts, rest))
                                           in
                                        (match uu____11786 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12049 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12055  ->
                                        match uu___2_12055 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12058 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12066 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12066)))
                                in
                             if uu____12049
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___837_12088  ->
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
                   let uu____12127 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12127
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12146 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12146, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12202 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12202 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12208 = encode_sigelt' env se  in
      match uu____12208 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12220 =
                  let uu____12223 =
                    let uu____12224 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12224  in
                  [uu____12223]  in
                FStar_All.pipe_right uu____12220
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12229 ->
                let uu____12230 =
                  let uu____12233 =
                    let uu____12236 =
                      let uu____12237 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12237  in
                    [uu____12236]  in
                  FStar_All.pipe_right uu____12233
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12244 =
                  let uu____12247 =
                    let uu____12250 =
                      let uu____12253 =
                        let uu____12254 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12254  in
                      [uu____12253]  in
                    FStar_All.pipe_right uu____12250
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12247  in
                FStar_List.append uu____12230 uu____12244
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12268 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12268
       then
         let uu____12273 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12273
       else ());
      (let is_opaque_to_smt t =
         let uu____12285 =
           let uu____12286 = FStar_Syntax_Subst.compress t  in
           uu____12286.FStar_Syntax_Syntax.n  in
         match uu____12285 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12291)) -> s = "opaque_to_smt"
         | uu____12296 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12305 =
           let uu____12306 = FStar_Syntax_Subst.compress t  in
           uu____12306.FStar_Syntax_Syntax.n  in
         match uu____12305 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12311)) -> s = "uninterpreted_by_smt"
         | uu____12316 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12322 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12328 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12340 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12341 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12342 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12355 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12357 =
             let uu____12359 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12359  in
           if uu____12357
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12388 ->
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
                  let uu____12421 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____12421  in
                let uu____12422 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12422 with
                | (formals,uu____12442) ->
                    let arity = FStar_List.length formals  in
                    let uu____12466 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12466 with
                     | (aname,atok,env2) ->
                         let uu____12488 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____12488 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12504 =
                                  let uu____12505 =
                                    let uu____12517 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____12537  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12517,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12505
                                   in
                                [uu____12504;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____12554 =
                                let aux uu____12600 uu____12601 =
                                  match (uu____12600, uu____12601) with
                                  | ((bv,uu____12645),(env3,acc_sorts,acc))
                                      ->
                                      let uu____12677 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____12677 with
                                       | (xxsym,xx,env4) ->
                                           let uu____12700 =
                                             let uu____12703 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____12703 :: acc_sorts  in
                                           (env4, uu____12700, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____12554 with
                               | (uu____12735,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____12751 =
                                       let uu____12759 =
                                         let uu____12760 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12761 =
                                           let uu____12772 =
                                             let uu____12773 =
                                               let uu____12778 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____12778)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____12773
                                              in
                                           ([[app]], xs_sorts, uu____12772)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12760 uu____12761
                                          in
                                       (uu____12759,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12751
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____12793 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____12793
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____12796 =
                                       let uu____12804 =
                                         let uu____12805 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12806 =
                                           let uu____12817 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____12817)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12805 uu____12806
                                          in
                                       (uu____12804,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12796
                                      in
                                   let uu____12830 =
                                     let uu____12833 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____12833  in
                                   (env2, uu____12830))))
                 in
              let uu____12842 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____12842 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12868,uu____12869)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____12870 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____12870 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12892,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____12899 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_12905  ->
                       match uu___3_12905 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____12908 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____12914 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____12917 -> false))
                in
             Prims.op_Negation uu____12899  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____12927 =
                let uu____12932 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____12932 env fv t quals  in
              match uu____12927 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____12946 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____12946  in
                  let uu____12949 =
                    let uu____12950 =
                      let uu____12953 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____12953
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____12950  in
                  (uu____12949, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____12963 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____12963 with
            | (uvs,f1) ->
                let env1 =
                  let uu___974_12975 = env  in
                  let uu____12976 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___974_12975.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___974_12975.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___974_12975.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____12976;
                    FStar_SMTEncoding_Env.warn =
                      (uu___974_12975.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___974_12975.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___974_12975.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___974_12975.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___974_12975.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___974_12975.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___974_12975.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____12978 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____12978 with
                 | (f3,decls) ->
                     let g =
                       let uu____12992 =
                         let uu____12995 =
                           let uu____12996 =
                             let uu____13004 =
                               let uu____13005 =
                                 let uu____13007 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13007
                                  in
                               FStar_Pervasives_Native.Some uu____13005  in
                             let uu____13011 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13004, uu____13011)  in
                           FStar_SMTEncoding_Util.mkAssume uu____12996  in
                         [uu____12995]  in
                       FStar_All.pipe_right uu____12992
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13020) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13034 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13056 =
                        let uu____13059 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13059.FStar_Syntax_Syntax.fv_name  in
                      uu____13056.FStar_Syntax_Syntax.v  in
                    let uu____13060 =
                      let uu____13062 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13062  in
                    if uu____13060
                    then
                      let val_decl =
                        let uu___991_13094 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___991_13094.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___991_13094.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___991_13094.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____13095 = encode_sigelt' env1 val_decl  in
                      match uu____13095 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13034 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13131,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13133;
                           FStar_Syntax_Syntax.lbtyp = uu____13134;
                           FStar_Syntax_Syntax.lbeff = uu____13135;
                           FStar_Syntax_Syntax.lbdef = uu____13136;
                           FStar_Syntax_Syntax.lbattrs = uu____13137;
                           FStar_Syntax_Syntax.lbpos = uu____13138;_}::[]),uu____13139)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13158 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____13158 with
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
                  let uu____13196 =
                    let uu____13199 =
                      let uu____13200 =
                        let uu____13208 =
                          let uu____13209 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13210 =
                            let uu____13221 =
                              let uu____13222 =
                                let uu____13227 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13227)  in
                              FStar_SMTEncoding_Util.mkEq uu____13222  in
                            ([[b2t_x]], [xx], uu____13221)  in
                          FStar_SMTEncoding_Term.mkForall uu____13209
                            uu____13210
                           in
                        (uu____13208,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13200  in
                    [uu____13199]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13196
                   in
                let uu____13265 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13265, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13268,uu____13269) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13279  ->
                   match uu___4_13279 with
                   | FStar_Syntax_Syntax.Discriminator uu____13281 -> true
                   | uu____13283 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13285,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13297 =
                      let uu____13299 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13299.FStar_Ident.idText  in
                    uu____13297 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13306  ->
                      match uu___5_13306 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13309 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13312) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13326  ->
                   match uu___6_13326 with
                   | FStar_Syntax_Syntax.Projector uu____13328 -> true
                   | uu____13334 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13338 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13338 with
            | FStar_Pervasives_Native.Some uu____13345 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1056_13347 = se  in
                  let uu____13348 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13348;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1056_13347.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1056_13347.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1056_13347.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13351) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1068_13372 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1068_13372.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1068_13372.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1068_13372.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1068_13372.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1068_13372.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13377) ->
           let uu____13386 = encode_sigelts env ses  in
           (match uu____13386 with
            | (g,env1) ->
                let uu____13397 =
                  FStar_List.fold_left
                    (fun uu____13421  ->
                       fun elt  ->
                         match uu____13421 with
                         | (g',inversions) ->
                             let uu____13449 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_13472  ->
                                       match uu___7_13472 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13474;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13475;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13476;_}
                                           -> false
                                       | uu____13483 -> true))
                                in
                             (match uu____13449 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1094_13508 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1094_13508.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1094_13508.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1094_13508.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13397 with
                 | (g',inversions) ->
                     let uu____13527 =
                       FStar_List.fold_left
                         (fun uu____13558  ->
                            fun elt  ->
                              match uu____13558 with
                              | (decls,elts,rest) ->
                                  let uu____13599 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_13608  ->
                                            match uu___8_13608 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____13610 -> true
                                            | uu____13623 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____13599
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____13646 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_13667  ->
                                               match uu___9_13667 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____13669 -> true
                                               | uu____13682 -> false))
                                        in
                                     match uu____13646 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1116_13713 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1116_13713.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1116_13713.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1116_13713.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____13527 with
                      | (decls,elts,rest) ->
                          let uu____13739 =
                            let uu____13740 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____13747 =
                              let uu____13750 =
                                let uu____13753 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____13753  in
                              FStar_List.append elts uu____13750  in
                            FStar_List.append uu____13740 uu____13747  in
                          (uu____13739, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____13764,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____13777 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____13777 with
             | (usubst,uvs) ->
                 let uu____13797 =
                   let uu____13804 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____13805 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____13806 =
                     let uu____13807 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____13807 k  in
                   (uu____13804, uu____13805, uu____13806)  in
                 (match uu____13797 with
                  | (env1,tps1,k1) ->
                      let uu____13820 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____13820 with
                       | (tps2,k2) ->
                           let uu____13828 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____13828 with
                            | (uu____13844,k3) ->
                                let uu____13866 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____13866 with
                                 | (tps3,env_tps,uu____13878,us) ->
                                     let u_k =
                                       let uu____13881 =
                                         let uu____13882 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____13883 =
                                           let uu____13888 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____13890 =
                                             let uu____13891 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____13891
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____13888 uu____13890
                                            in
                                         uu____13883
                                           FStar_Pervasives_Native.None
                                           uu____13882
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____13881 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____13909) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____13915,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____13918) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____13926,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____13933) ->
                                           let uu____13934 =
                                             let uu____13936 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13936
                                              in
                                           failwith uu____13934
                                       | (uu____13940,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____13941 =
                                             let uu____13943 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13943
                                              in
                                           failwith uu____13941
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____13947,uu____13948) ->
                                           let uu____13957 =
                                             let uu____13959 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13959
                                              in
                                           failwith uu____13957
                                       | (uu____13963,FStar_Syntax_Syntax.U_unif
                                          uu____13964) ->
                                           let uu____13973 =
                                             let uu____13975 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13975
                                              in
                                           failwith uu____13973
                                       | uu____13979 -> false  in
                                     let u_leq_u_k u =
                                       let uu____13992 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____13992 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14010 = u_leq_u_k u_tp  in
                                       if uu____14010
                                       then true
                                       else
                                         (let uu____14017 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14017 with
                                          | (formals,uu____14034) ->
                                              let uu____14055 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14055 with
                                               | (uu____14065,uu____14066,uu____14067,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14078 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14078
             then
               let uu____14083 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14083
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14103  ->
                       match uu___10_14103 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14107 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14120 = c  in
                 match uu____14120 with
                 | (name,args,uu____14125,uu____14126,uu____14127) ->
                     let uu____14138 =
                       let uu____14139 =
                         let uu____14151 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14178  ->
                                   match uu____14178 with
                                   | (uu____14187,sort,uu____14189) -> sort))
                            in
                         (name, uu____14151,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14139  in
                     [uu____14138]
               else
                 (let uu____14200 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14200 c)
                in
             let inversion_axioms tapp vars =
               let uu____14218 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14226 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14226 FStar_Option.isNone))
                  in
               if uu____14218
               then []
               else
                 (let uu____14261 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14261 with
                  | (xxsym,xx) ->
                      let uu____14274 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14313  ->
                                fun l  ->
                                  match uu____14313 with
                                  | (out,decls) ->
                                      let uu____14333 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14333 with
                                       | (uu____14344,data_t) ->
                                           let uu____14346 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14346 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14390 =
                                                    let uu____14391 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14391.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14390 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14394,indices)
                                                      -> indices
                                                  | uu____14420 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14450  ->
                                                            match uu____14450
                                                            with
                                                            | (x,uu____14458)
                                                                ->
                                                                let uu____14463
                                                                  =
                                                                  let uu____14464
                                                                    =
                                                                    let uu____14472
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14472,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14464
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14463)
                                                       env)
                                                   in
                                                let uu____14477 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14477 with
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
                                                                  let uu____14512
                                                                    =
                                                                    let uu____14517
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____14517,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____14512)
                                                             vars indices1
                                                         else []  in
                                                       let uu____14520 =
                                                         let uu____14521 =
                                                           let uu____14526 =
                                                             let uu____14527
                                                               =
                                                               let uu____14532
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____14533
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____14532,
                                                                 uu____14533)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____14527
                                                              in
                                                           (out, uu____14526)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____14521
                                                          in
                                                       (uu____14520,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14274 with
                       | (data_ax,decls) ->
                           let uu____14548 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____14548 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____14565 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____14565 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____14572 =
                                    let uu____14580 =
                                      let uu____14581 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____14582 =
                                        let uu____14593 =
                                          let uu____14594 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____14596 =
                                            let uu____14599 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____14599 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____14594 uu____14596
                                           in
                                        let uu____14601 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____14593,
                                          uu____14601)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____14581 uu____14582
                                       in
                                    let uu____14610 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____14580,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____14610)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____14572
                                   in
                                let uu____14616 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____14616)))
                in
             let uu____14623 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____14645 ->
                     let uu____14646 =
                       let uu____14653 =
                         let uu____14654 =
                           let uu____14669 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____14669)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____14654  in
                       FStar_Syntax_Syntax.mk uu____14653  in
                     uu____14646 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____14623 with
             | (formals,res) ->
                 let uu____14709 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____14709 with
                  | (vars,guards,env',binder_decls,uu____14734) ->
                      let arity = FStar_List.length vars  in
                      let uu____14748 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____14748 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____14774 =
                               let uu____14782 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____14782)  in
                             FStar_SMTEncoding_Util.mkApp uu____14774  in
                           let uu____14788 =
                             let tname_decl =
                               let uu____14798 =
                                 let uu____14799 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____14818 =
                                             let uu____14820 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____14820
                                              in
                                           let uu____14822 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____14818, uu____14822, false)))
                                    in
                                 let uu____14826 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____14799,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____14826, false)
                                  in
                               constructor_or_logic_type_decl uu____14798  in
                             let uu____14834 =
                               match vars with
                               | [] ->
                                   let uu____14847 =
                                     let uu____14848 =
                                       let uu____14851 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _14857  ->
                                            FStar_Pervasives_Native.Some
                                              _14857) uu____14851
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____14848
                                      in
                                   ([], uu____14847)
                               | uu____14860 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____14870 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____14870
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____14886 =
                                       let uu____14894 =
                                         let uu____14895 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14896 =
                                           let uu____14912 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____14912)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____14895 uu____14896
                                          in
                                       (uu____14894,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____14886
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____14834 with
                             | (tok_decls,env2) ->
                                 let uu____14939 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____14939
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____14788 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____14967 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____14967 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____14989 =
                                            let uu____14990 =
                                              let uu____14998 =
                                                let uu____14999 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____14999
                                                 in
                                              (uu____14998,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____14990
                                             in
                                          [uu____14989]
                                        else []  in
                                      let uu____15007 =
                                        let uu____15010 =
                                          let uu____15013 =
                                            let uu____15016 =
                                              let uu____15017 =
                                                let uu____15025 =
                                                  let uu____15026 =
                                                    FStar_Ident.range_of_lid
                                                      t
                                                     in
                                                  let uu____15027 =
                                                    let uu____15038 =
                                                      FStar_SMTEncoding_Util.mkImp
                                                        (guard, k1)
                                                       in
                                                    ([[tapp]], vars,
                                                      uu____15038)
                                                     in
                                                  FStar_SMTEncoding_Term.mkForall
                                                    uu____15026 uu____15027
                                                   in
                                                (uu____15025,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15017
                                               in
                                            [uu____15016]  in
                                          FStar_List.append karr uu____15013
                                           in
                                        FStar_All.pipe_right uu____15010
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15007
                                   in
                                let aux =
                                  let uu____15057 =
                                    let uu____15060 =
                                      inversion_axioms tapp vars  in
                                    let uu____15063 =
                                      let uu____15066 =
                                        let uu____15069 =
                                          let uu____15070 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15070 env2 tapp
                                            vars
                                           in
                                        [uu____15069]  in
                                      FStar_All.pipe_right uu____15066
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15060 uu____15063
                                     in
                                  FStar_List.append kindingAx uu____15057  in
                                let g =
                                  let uu____15078 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15078
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15086,uu____15087,uu____15088,uu____15089,uu____15090)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15098,t,uu____15100,n_tps,uu____15102) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15113 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15113 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15161 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15161 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15185 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15185 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15205 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15205 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15284 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15284,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15291 =
                                   let uu____15292 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15292, true)
                                    in
                                 let uu____15300 =
                                   let uu____15307 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15307
                                    in
                                 FStar_All.pipe_right uu____15291 uu____15300
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
                               let uu____15319 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15319 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15331::uu____15332 ->
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
                                            let uu____15381 =
                                              let uu____15382 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15382]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15381
                                             in
                                          let uu____15408 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15409 =
                                            let uu____15420 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15420)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15408 uu____15409
                                      | uu____15447 -> tok_typing  in
                                    let uu____15458 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15458 with
                                     | (vars',guards',env'',decls_formals,uu____15483)
                                         ->
                                         let uu____15496 =
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
                                         (match uu____15496 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____15526 ->
                                                    let uu____15535 =
                                                      let uu____15536 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____15536
                                                       in
                                                    [uu____15535]
                                                 in
                                              let encode_elim uu____15552 =
                                                let uu____15553 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____15553 with
                                                | (head1,args) ->
                                                    let uu____15604 =
                                                      let uu____15605 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____15605.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____15604 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____15617;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____15618;_},uu____15619)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____15625 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____15625
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
                                                                  | uu____15688
                                                                    ->
                                                                    let uu____15689
                                                                    =
                                                                    let uu____15695
                                                                    =
                                                                    let uu____15697
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15697
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15695)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15689
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15720
                                                                    =
                                                                    let uu____15722
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15722
                                                                     in
                                                                    if
                                                                    uu____15720
                                                                    then
                                                                    let uu____15744
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15744]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____15747
                                                                =
                                                                let uu____15761
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____15818
                                                                     ->
                                                                    fun
                                                                    uu____15819
                                                                     ->
                                                                    match 
                                                                    (uu____15818,
                                                                    uu____15819)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15930
                                                                    =
                                                                    let uu____15938
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15938
                                                                     in
                                                                    (match uu____15930
                                                                    with
                                                                    | 
                                                                    (uu____15952,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15963
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15963
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15968
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15968
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
                                                                  uu____15761
                                                                 in
                                                              (match uu____15747
                                                               with
                                                               | (uu____15989,arg_vars,elim_eqns_or_guards,uu____15992)
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
                                                                    let uu____16019
                                                                    =
                                                                    let uu____16027
                                                                    =
                                                                    let uu____16028
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16029
                                                                    =
                                                                    let uu____16040
                                                                    =
                                                                    let uu____16041
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16041
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16043
                                                                    =
                                                                    let uu____16044
                                                                    =
                                                                    let uu____16049
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16049)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16044
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16040,
                                                                    uu____16043)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16028
                                                                    uu____16029
                                                                     in
                                                                    (uu____16027,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16019
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16064
                                                                    =
                                                                    let uu____16065
                                                                    =
                                                                    let uu____16071
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16071,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16065
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16064
                                                                     in
                                                                    let uu____16074
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16074
                                                                    then
                                                                    let x =
                                                                    let uu____16078
                                                                    =
                                                                    let uu____16084
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16084,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16078
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16089
                                                                    =
                                                                    let uu____16097
                                                                    =
                                                                    let uu____16098
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16099
                                                                    =
                                                                    let uu____16110
                                                                    =
                                                                    let uu____16115
                                                                    =
                                                                    let uu____16118
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16118]
                                                                     in
                                                                    [uu____16115]
                                                                     in
                                                                    let uu____16123
                                                                    =
                                                                    let uu____16124
                                                                    =
                                                                    let uu____16129
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16131
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16129,
                                                                    uu____16131)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16124
                                                                     in
                                                                    (uu____16110,
                                                                    [x],
                                                                    uu____16123)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16098
                                                                    uu____16099
                                                                     in
                                                                    let uu____16152
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16097,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16152)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16089
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16163
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
                                                                    (let uu____16186
                                                                    =
                                                                    let uu____16187
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16187
                                                                    dapp1  in
                                                                    [uu____16186])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16163
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16194
                                                                    =
                                                                    let uu____16202
                                                                    =
                                                                    let uu____16203
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16204
                                                                    =
                                                                    let uu____16215
                                                                    =
                                                                    let uu____16216
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16216
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16218
                                                                    =
                                                                    let uu____16219
                                                                    =
                                                                    let uu____16224
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16224)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16219
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16215,
                                                                    uu____16218)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16203
                                                                    uu____16204
                                                                     in
                                                                    (uu____16202,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16194)
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
                                                         let uu____16243 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16243
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
                                                                  | uu____16306
                                                                    ->
                                                                    let uu____16307
                                                                    =
                                                                    let uu____16313
                                                                    =
                                                                    let uu____16315
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16315
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16313)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16307
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16338
                                                                    =
                                                                    let uu____16340
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16340
                                                                     in
                                                                    if
                                                                    uu____16338
                                                                    then
                                                                    let uu____16362
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16362]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16365
                                                                =
                                                                let uu____16379
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16436
                                                                     ->
                                                                    fun
                                                                    uu____16437
                                                                     ->
                                                                    match 
                                                                    (uu____16436,
                                                                    uu____16437)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16548
                                                                    =
                                                                    let uu____16556
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16556
                                                                     in
                                                                    (match uu____16548
                                                                    with
                                                                    | 
                                                                    (uu____16570,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16581
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16581
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16586
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16586
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
                                                                  uu____16379
                                                                 in
                                                              (match uu____16365
                                                               with
                                                               | (uu____16607,arg_vars,elim_eqns_or_guards,uu____16610)
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
                                                                    let uu____16637
                                                                    =
                                                                    let uu____16645
                                                                    =
                                                                    let uu____16646
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16647
                                                                    =
                                                                    let uu____16658
                                                                    =
                                                                    let uu____16659
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16659
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16661
                                                                    =
                                                                    let uu____16662
                                                                    =
                                                                    let uu____16667
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16667)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16662
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16658,
                                                                    uu____16661)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16646
                                                                    uu____16647
                                                                     in
                                                                    (uu____16645,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16637
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16682
                                                                    =
                                                                    let uu____16683
                                                                    =
                                                                    let uu____16689
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16689,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16683
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16682
                                                                     in
                                                                    let uu____16692
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16692
                                                                    then
                                                                    let x =
                                                                    let uu____16696
                                                                    =
                                                                    let uu____16702
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16702,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16696
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16707
                                                                    =
                                                                    let uu____16715
                                                                    =
                                                                    let uu____16716
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16717
                                                                    =
                                                                    let uu____16728
                                                                    =
                                                                    let uu____16733
                                                                    =
                                                                    let uu____16736
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16736]
                                                                     in
                                                                    [uu____16733]
                                                                     in
                                                                    let uu____16741
                                                                    =
                                                                    let uu____16742
                                                                    =
                                                                    let uu____16747
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16749
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16747,
                                                                    uu____16749)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16742
                                                                     in
                                                                    (uu____16728,
                                                                    [x],
                                                                    uu____16741)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16716
                                                                    uu____16717
                                                                     in
                                                                    let uu____16770
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16715,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16770)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16707
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16781
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
                                                                    (let uu____16804
                                                                    =
                                                                    let uu____16805
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16805
                                                                    dapp1  in
                                                                    [uu____16804])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16781
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16812
                                                                    =
                                                                    let uu____16820
                                                                    =
                                                                    let uu____16821
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16822
                                                                    =
                                                                    let uu____16833
                                                                    =
                                                                    let uu____16834
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16834
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16836
                                                                    =
                                                                    let uu____16837
                                                                    =
                                                                    let uu____16842
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16842)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16837
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16833,
                                                                    uu____16836)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16821
                                                                    uu____16822
                                                                     in
                                                                    (uu____16820,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16812)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____16859 ->
                                                         ((let uu____16861 =
                                                             let uu____16867
                                                               =
                                                               let uu____16869
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____16871
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____16869
                                                                 uu____16871
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____16867)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____16861);
                                                          ([], [])))
                                                 in
                                              let uu____16879 =
                                                encode_elim ()  in
                                              (match uu____16879 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____16905 =
                                                       let uu____16908 =
                                                         let uu____16911 =
                                                           let uu____16914 =
                                                             let uu____16917
                                                               =
                                                               let uu____16920
                                                                 =
                                                                 let uu____16923
                                                                   =
                                                                   let uu____16924
                                                                    =
                                                                    let uu____16936
                                                                    =
                                                                    let uu____16937
                                                                    =
                                                                    let uu____16939
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16939
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____16937
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____16936)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____16924
                                                                    in
                                                                 [uu____16923]
                                                                  in
                                                               FStar_List.append
                                                                 uu____16920
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____16917
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____16950 =
                                                             let uu____16953
                                                               =
                                                               let uu____16956
                                                                 =
                                                                 let uu____16959
                                                                   =
                                                                   let uu____16962
                                                                    =
                                                                    let uu____16965
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____16970
                                                                    =
                                                                    let uu____16973
                                                                    =
                                                                    let uu____16974
                                                                    =
                                                                    let uu____16982
                                                                    =
                                                                    let uu____16983
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16984
                                                                    =
                                                                    let uu____16995
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16995)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16983
                                                                    uu____16984
                                                                     in
                                                                    (uu____16982,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16974
                                                                     in
                                                                    let uu____17008
                                                                    =
                                                                    let uu____17011
                                                                    =
                                                                    let uu____17012
                                                                    =
                                                                    let uu____17020
                                                                    =
                                                                    let uu____17021
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17022
                                                                    =
                                                                    let uu____17033
                                                                    =
                                                                    let uu____17034
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17034
                                                                    vars'  in
                                                                    let uu____17036
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17033,
                                                                    uu____17036)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17021
                                                                    uu____17022
                                                                     in
                                                                    (uu____17020,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17012
                                                                     in
                                                                    [uu____17011]
                                                                     in
                                                                    uu____16973
                                                                    ::
                                                                    uu____17008
                                                                     in
                                                                    uu____16965
                                                                    ::
                                                                    uu____16970
                                                                     in
                                                                   FStar_List.append
                                                                    uu____16962
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____16959
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____16956
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____16953
                                                              in
                                                           FStar_List.append
                                                             uu____16914
                                                             uu____16950
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____16911
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____16908
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____16905
                                                      in
                                                   let uu____17053 =
                                                     let uu____17054 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17054 g
                                                      in
                                                   (uu____17053, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17088  ->
              fun se  ->
                match uu____17088 with
                | (g,env1) ->
                    let uu____17108 = encode_sigelt env1 se  in
                    (match uu____17108 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17176 =
        match uu____17176 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17213 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17221 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17221
                   then
                     let uu____17226 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17228 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17230 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17226 uu____17228 uu____17230
                   else ());
                  (let uu____17235 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17235 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17253 =
                         let uu____17261 =
                           let uu____17263 =
                             let uu____17265 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17265
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17263  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17261
                          in
                       (match uu____17253 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17285 = FStar_Options.log_queries ()
                                 in
                              if uu____17285
                              then
                                let uu____17288 =
                                  let uu____17290 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17292 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17294 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17290 uu____17292 uu____17294
                                   in
                                FStar_Pervasives_Native.Some uu____17288
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17310 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17320 =
                                let uu____17323 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17323  in
                              FStar_List.append uu____17310 uu____17320  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17335,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17355 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17355 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____17376 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____17376 with | (uu____17403,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17456  ->
              match uu____17456 with
              | (l,uu____17465,uu____17466) ->
                  let uu____17469 =
                    let uu____17481 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17481, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17469))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17514  ->
              match uu____17514 with
              | (l,uu____17525,uu____17526) ->
                  let uu____17529 =
                    let uu____17530 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _17533  -> FStar_SMTEncoding_Term.Echo _17533)
                      uu____17530
                     in
                  let uu____17534 =
                    let uu____17537 =
                      let uu____17538 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17538  in
                    [uu____17537]  in
                  uu____17529 :: uu____17534))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17556 =
      let uu____17559 =
        let uu____17560 = FStar_Util.psmap_empty ()  in
        let uu____17575 =
          let uu____17584 = FStar_Util.psmap_empty ()  in (uu____17584, [])
           in
        let uu____17591 =
          let uu____17593 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____17593 FStar_Ident.string_of_lid  in
        let uu____17595 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17560;
          FStar_SMTEncoding_Env.fvar_bindings = uu____17575;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____17591;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____17595
        }  in
      [uu____17559]  in
    FStar_ST.op_Colon_Equals last_env uu____17556
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____17639 = FStar_ST.op_Bang last_env  in
      match uu____17639 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17667 ->
          let uu___1540_17670 = e  in
          let uu____17671 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1540_17670.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1540_17670.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1540_17670.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1540_17670.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1540_17670.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1540_17670.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1540_17670.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____17671;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1540_17670.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1540_17670.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____17679 = FStar_ST.op_Bang last_env  in
    match uu____17679 with
    | [] -> failwith "Empty env stack"
    | uu____17706::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____17738  ->
    let uu____17739 = FStar_ST.op_Bang last_env  in
    match uu____17739 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____17799  ->
    let uu____17800 = FStar_ST.op_Bang last_env  in
    match uu____17800 with
    | [] -> failwith "Popping an empty stack"
    | uu____17827::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____17864  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____17917  ->
         let uu____17918 = snapshot_env ()  in
         match uu____17918 with
         | (env_depth,()) ->
             let uu____17940 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____17940 with
              | (varops_depth,()) ->
                  let uu____17962 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____17962 with
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
        (fun uu____18020  ->
           let uu____18021 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18021 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18116 = snapshot msg  in () 
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
        | (uu____18162::uu____18163,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1601_18171 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1601_18171.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1601_18171.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1601_18171.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18172 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1607_18199 = elt  in
        let uu____18200 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1607_18199.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1607_18199.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18200;
          FStar_SMTEncoding_Term.a_names =
            (uu___1607_18199.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18220 =
        let uu____18223 =
          let uu____18224 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18224  in
        let uu____18225 = open_fact_db_tags env  in uu____18223 ::
          uu____18225
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18220
  
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
      let uu____18252 = encode_sigelt env se  in
      match uu____18252 with
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
                (let uu____18298 =
                   let uu____18301 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18301
                    in
                 match uu____18298 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18316 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18316
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18346 = FStar_Options.log_queries ()  in
        if uu____18346
        then
          let uu____18351 =
            let uu____18352 =
              let uu____18354 =
                let uu____18356 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18356 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18354  in
            FStar_SMTEncoding_Term.Caption uu____18352  in
          uu____18351 :: decls
        else decls  in
      (let uu____18375 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18375
       then
         let uu____18378 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18378
       else ());
      (let env =
         let uu____18384 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18384 tcenv  in
       let uu____18385 = encode_top_level_facts env se  in
       match uu____18385 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18399 =
               let uu____18402 =
                 let uu____18405 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18405
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18402  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18399)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18438 = FStar_Options.log_queries ()  in
          if uu____18438
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1645_18458 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1645_18458.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1645_18458.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1645_18458.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1645_18458.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1645_18458.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1645_18458.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1645_18458.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1645_18458.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1645_18458.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1645_18458.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18463 =
             let uu____18466 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18466
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18463  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18486 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18486
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
          (let uu____18510 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____18510
           then
             let uu____18513 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____18513
           else ());
          (let env =
             let uu____18521 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____18521
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____18560  ->
                     fun se  ->
                       match uu____18560 with
                       | (g,env2) ->
                           let uu____18580 = encode_top_level_facts env2 se
                              in
                           (match uu____18580 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____18603 =
             encode_signature
               (let uu___1668_18612 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1668_18612.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1668_18612.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1668_18612.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1668_18612.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1668_18612.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1668_18612.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1668_18612.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1668_18612.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1668_18612.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1668_18612.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____18603 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____18628 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18628
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____18634 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____18634))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____18662  ->
        match uu____18662 with
        | (decls,fvbs) ->
            ((let uu____18676 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____18676
              then ()
              else
                (let uu____18681 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18681
                 then
                   let uu____18684 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____18684
                 else ()));
             (let env =
                let uu____18692 = get_env name tcenv  in
                FStar_All.pipe_right uu____18692
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____18694 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____18694
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____18708 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____18708
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
        (let uu____18770 =
           let uu____18772 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____18772.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____18770);
        (let env =
           let uu____18774 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____18774 tcenv  in
         let uu____18775 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____18814 = aux rest  in
                 (match uu____18814 with
                  | (out,rest1) ->
                      let t =
                        let uu____18842 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____18842 with
                        | FStar_Pervasives_Native.Some uu____18845 ->
                            let uu____18846 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____18846
                              x.FStar_Syntax_Syntax.sort
                        | uu____18847 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____18851 =
                        let uu____18854 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1709_18857 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1709_18857.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1709_18857.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____18854 :: out  in
                      (uu____18851, rest1))
             | uu____18862 -> ([], bindings)  in
           let uu____18869 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____18869 with
           | (closing,bindings) ->
               let uu____18896 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____18896, bindings)
            in
         match uu____18775 with
         | (q1,bindings) ->
             let uu____18927 = encode_env_bindings env bindings  in
             (match uu____18927 with
              | (env_decls,env1) ->
                  ((let uu____18949 =
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
                    if uu____18949
                    then
                      let uu____18956 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____18956
                    else ());
                   (let uu____18961 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____18961 with
                    | (phi,qdecls) ->
                        let uu____18982 =
                          let uu____18987 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____18987 phi
                           in
                        (match uu____18982 with
                         | (labels,phi1) ->
                             let uu____19004 = encode_labels labels  in
                             (match uu____19004 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19040 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19040
                                    then
                                      let uu____19045 =
                                        let uu____19046 =
                                          let uu____19048 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____19048
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19046
                                         in
                                      [uu____19045]
                                    else []  in
                                  let query_prelude =
                                    let uu____19056 =
                                      let uu____19057 =
                                        let uu____19058 =
                                          let uu____19061 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19068 =
                                            let uu____19071 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19071
                                             in
                                          FStar_List.append uu____19061
                                            uu____19068
                                           in
                                        FStar_List.append env_decls
                                          uu____19058
                                         in
                                      FStar_All.pipe_right uu____19057
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19056
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19081 =
                                      let uu____19089 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19090 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19089,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19090)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19081
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
  