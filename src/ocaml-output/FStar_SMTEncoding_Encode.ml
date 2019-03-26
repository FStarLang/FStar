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
                                                  let uu____7765 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____7765
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____7776 ->
                                                  let uu____7785 =
                                                    let uu____7793 =
                                                      get_vtok ()  in
                                                    (uu____7793, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7785
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____7800 =
                                                let uu____7808 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____7808)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____7800
                                               in
                                            let uu____7822 =
                                              let vname_decl =
                                                let uu____7830 =
                                                  let uu____7842 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____7842,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____7830
                                                 in
                                              let uu____7853 =
                                                let env2 =
                                                  let uu___390_7859 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___390_7859.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____7860 =
                                                  let uu____7862 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____7862
                                                   in
                                                if uu____7860
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____7853 with
                                              | (tok_typing,decls2) ->
                                                  let uu____7879 =
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
                                                        let uu____7905 =
                                                          let uu____7908 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____7908
                                                           in
                                                        let uu____7915 =
                                                          let uu____7916 =
                                                            let uu____7919 =
                                                              let uu____7920
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____7920
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _7924  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _7924)
                                                              uu____7919
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____7916
                                                           in
                                                        (uu____7905,
                                                          uu____7915)
                                                    | uu____7927 when thunked
                                                        ->
                                                        let uu____7938 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____7938
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____7953
                                                                 =
                                                                 let uu____7961
                                                                   =
                                                                   let uu____7964
                                                                    =
                                                                    let uu____7967
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____7967]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____7964
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____7961)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____7953
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____7975 =
                                                               let uu____7983
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____7983,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7975
                                                              in
                                                           let uu____7988 =
                                                             let uu____7991 =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____7991
                                                              in
                                                           (uu____7988, env1))
                                                    | uu____8000 ->
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
                                                          let uu____8024 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____8025 =
                                                            let uu____8036 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____8036)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____8024
                                                            uu____8025
                                                           in
                                                        let name_tok_corr =
                                                          let uu____8046 =
                                                            let uu____8054 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____8054,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8046
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
                                                          let vtok_fv =
                                                            FStar_SMTEncoding_Term.mk_fv
                                                              (vtok,
                                                                FStar_SMTEncoding_Term.Term_sort)
                                                             in
                                                          let vtok_app_r =
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f [vtok_fv]
                                                             in
                                                          let vtok_app_l =
                                                            let uu____8084 =
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                vtok_fv
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              uu____8084 
                                                              [ff]
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8102 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8103 =
                                                              let uu____8114
                                                                =
                                                                let uu____8115
                                                                  =
                                                                  let uu____8120
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8121
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8120,
                                                                    uu____8121)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8115
                                                                 in
                                                              ([[vtok_app_r];
                                                               [vtok_app_l]],
                                                                [ff],
                                                                uu____8114)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8102
                                                              uu____8103
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8152 =
                                                          let uu____8155 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8155
                                                           in
                                                        (uu____8152, env1)
                                                     in
                                                  (match uu____7879 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8176 =
                                                         let uu____8179 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8179
                                                           tok_decl
                                                          in
                                                       (uu____8176, env2))
                                               in
                                            (match uu____7822 with
                                             | (decls2,env2) ->
                                                 let uu____8198 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8208 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8208 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8223 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8223, decls)
                                                    in
                                                 (match uu____8198 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8238 =
                                                          let uu____8246 =
                                                            let uu____8247 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8248 =
                                                              let uu____8259
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8259)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8247
                                                              uu____8248
                                                             in
                                                          (uu____8246,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8238
                                                         in
                                                      let freshness =
                                                        let uu____8275 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8275
                                                        then
                                                          let uu____8283 =
                                                            let uu____8284 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8285 =
                                                              let uu____8298
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8305
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8298,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8305)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8284
                                                              uu____8285
                                                             in
                                                          let uu____8311 =
                                                            let uu____8314 =
                                                              let uu____8315
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8315
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8314]  in
                                                          uu____8283 ::
                                                            uu____8311
                                                        else []  in
                                                      let g =
                                                        let uu____8321 =
                                                          let uu____8324 =
                                                            let uu____8327 =
                                                              let uu____8330
                                                                =
                                                                let uu____8333
                                                                  =
                                                                  let uu____8336
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8336
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8333
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8330
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8327
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8324
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8321
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
          let uu____8376 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8376 with
          | FStar_Pervasives_Native.None  ->
              let uu____8387 = encode_free_var false env x t t_norm []  in
              (match uu____8387 with
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
            let uu____8450 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8450 with
            | (decls,env1) ->
                let uu____8461 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8461
                then
                  let uu____8468 =
                    let uu____8469 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8469  in
                  (uu____8468, env1)
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
             (fun uu____8525  ->
                fun lb  ->
                  match uu____8525 with
                  | (decls,env1) ->
                      let uu____8545 =
                        let uu____8550 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8550
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8545 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8579 = FStar_Syntax_Util.head_and_args t  in
    match uu____8579 with
    | (hd1,args) ->
        let uu____8623 =
          let uu____8624 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8624.FStar_Syntax_Syntax.n  in
        (match uu____8623 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8630,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____8654 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____8665 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___479_8673 = en  in
    let uu____8674 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___479_8673.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___479_8673.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___479_8673.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___479_8673.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___479_8673.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___479_8673.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___479_8673.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___479_8673.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___479_8673.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___479_8673.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____8674
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____8704  ->
      fun quals  ->
        match uu____8704 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8809 = FStar_Util.first_N nbinders formals  in
              match uu____8809 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____8906  ->
                         fun uu____8907  ->
                           match (uu____8906, uu____8907) with
                           | ((formal,uu____8933),(binder,uu____8935)) ->
                               let uu____8956 =
                                 let uu____8963 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____8963)  in
                               FStar_Syntax_Syntax.NT uu____8956) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____8977 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____9018  ->
                              match uu____9018 with
                              | (x,i) ->
                                  let uu____9037 =
                                    let uu___505_9038 = x  in
                                    let uu____9039 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___505_9038.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___505_9038.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9039
                                    }  in
                                  (uu____9037, i)))
                       in
                    FStar_All.pipe_right uu____8977
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9063 =
                      let uu____9068 = FStar_Syntax_Subst.compress body  in
                      let uu____9069 =
                        let uu____9070 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9070
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____9068 uu____9069
                       in
                    uu____9063 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___512_9119 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___512_9119.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___512_9119.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___512_9119.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___512_9119.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___512_9119.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___512_9119.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___512_9119.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___512_9119.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___512_9119.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___512_9119.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___512_9119.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___512_9119.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___512_9119.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___512_9119.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___512_9119.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___512_9119.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___512_9119.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___512_9119.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___512_9119.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___512_9119.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___512_9119.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___512_9119.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___512_9119.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___512_9119.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___512_9119.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___512_9119.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___512_9119.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___512_9119.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___512_9119.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___512_9119.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___512_9119.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___512_9119.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___512_9119.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___512_9119.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___512_9119.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___512_9119.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___512_9119.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___512_9119.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___512_9119.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___512_9119.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___512_9119.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___512_9119.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____9191  ->
                       fun uu____9192  ->
                         match (uu____9191, uu____9192) with
                         | ((x,uu____9218),(b,uu____9220)) ->
                             let uu____9241 =
                               let uu____9248 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9248)  in
                             FStar_Syntax_Syntax.NT uu____9241) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9273 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9273
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9302 ->
                    let uu____9309 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9309
                | uu____9310 when Prims.op_Negation norm1 ->
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
                | uu____9313 ->
                    let uu____9314 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9314)
                 in
              let aux t1 e1 =
                let uu____9356 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9356 with
                | (binders,body,lopt) ->
                    let uu____9388 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9404 -> arrow_formals_comp_norm false t1  in
                    (match uu____9388 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9438 =
                           if nformals < nbinders
                           then
                             let uu____9472 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9472 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9552 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9552)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9582 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9582 with
                                | (binders1,body1) ->
                                    let uu____9635 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____9635))
                             else
                               (let uu____9648 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____9648))
                            in
                         (match uu____9438 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____9708 = aux t e  in
              match uu____9708 with
              | (binders,body,comp) ->
                  let uu____9754 =
                    let uu____9765 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____9765
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____9780 = aux comp1 body1  in
                      match uu____9780 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____9754 with
                   | (binders1,body1,comp1) ->
                       let uu____9863 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____9863, comp1))
               in
            (try
               (fun uu___582_9890  ->
                  match () with
                  | () ->
                      let uu____9897 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9897
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9913 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9976  ->
                                   fun lb  ->
                                     match uu____9976 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____10031 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____10031
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____10037 =
                                             let uu____10046 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____10046
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____10037 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9913 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10187;
                                    FStar_Syntax_Syntax.lbeff = uu____10188;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10190;
                                    FStar_Syntax_Syntax.lbpos = uu____10191;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10215 =
                                     let uu____10222 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10222 with
                                     | (tcenv',uu____10238,e_t) ->
                                         let uu____10244 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10255 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10244 with
                                          | (e1,t_norm1) ->
                                              ((let uu___645_10272 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___645_10272.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10215 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10282 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10282 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10302 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10302
                                               then
                                                 let uu____10307 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10310 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10307 uu____10310
                                               else ());
                                              (let uu____10315 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10315 with
                                               | (vars,_guards,env'1,binder_decls,uu____10342)
                                                   ->
                                                   let uu____10355 =
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
                                                         let uu____10372 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10372
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10394 =
                                                          let uu____10395 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10396 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10395 fvb
                                                            uu____10396
                                                           in
                                                        (vars, uu____10394))
                                                      in
                                                   (match uu____10355 with
                                                    | (vars1,app) ->
                                                        let uu____10407 =
                                                          let is_logical =
                                                            let uu____10420 =
                                                              let uu____10421
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10421.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10420
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10427 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10431 =
                                                              let uu____10432
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10432
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10431
                                                              (fun lid  ->
                                                                 let uu____10441
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10441
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10442 =
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
                                                          if uu____10442
                                                          then
                                                            let uu____10458 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10459 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10458,
                                                              uu____10459)
                                                          else
                                                            (let uu____10470
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10470))
                                                           in
                                                        (match uu____10407
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10494
                                                                 =
                                                                 let uu____10502
                                                                   =
                                                                   let uu____10503
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10504
                                                                    =
                                                                    let uu____10515
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10515)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10503
                                                                    uu____10504
                                                                    in
                                                                 let uu____10524
                                                                   =
                                                                   let uu____10525
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10525
                                                                    in
                                                                 (uu____10502,
                                                                   uu____10524,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10494
                                                                in
                                                             let uu____10531
                                                               =
                                                               let uu____10534
                                                                 =
                                                                 let uu____10537
                                                                   =
                                                                   let uu____10540
                                                                    =
                                                                    let uu____10543
                                                                    =
                                                                    let uu____10546
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10546
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10543
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10540
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10537
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10534
                                                                in
                                                             (uu____10531,
                                                               env2)))))))
                               | uu____10555 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10615 =
                                   let uu____10621 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____10621,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10615  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10627 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10680  ->
                                         fun fvb  ->
                                           match uu____10680 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10735 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10735
                                                  in
                                               let gtok =
                                                 let uu____10739 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10739
                                                  in
                                               let env4 =
                                                 let uu____10742 =
                                                   let uu____10745 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _10751  ->
                                                        FStar_Pervasives_Native.Some
                                                          _10751) uu____10745
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10742
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10627 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10871
                                     t_norm uu____10873 =
                                     match (uu____10871, uu____10873) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10903;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10904;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10906;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10907;_})
                                         ->
                                         let uu____10934 =
                                           let uu____10941 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10941 with
                                           | (tcenv',uu____10957,e_t) ->
                                               let uu____10963 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10974 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10963 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___732_10991 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___732_10991.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10934 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____11004 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____11004
                                                then
                                                  let uu____11009 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____11011 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____11013 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____11009 uu____11011
                                                    uu____11013
                                                else ());
                                               (let uu____11018 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____11018 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____11045 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____11045 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11067 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11067
                                                           then
                                                             let uu____11072
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11074
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11077
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11079
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11072
                                                               uu____11074
                                                               uu____11077
                                                               uu____11079
                                                           else ());
                                                          (let uu____11084 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11084
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11113)
                                                               ->
                                                               let uu____11126
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11139
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11139,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11143
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11143
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11156
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11156,
                                                                    decls0))
                                                                  in
                                                               (match uu____11126
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
                                                                    let uu____11177
                                                                    =
                                                                    let uu____11189
                                                                    =
                                                                    let uu____11192
                                                                    =
                                                                    let uu____11195
                                                                    =
                                                                    let uu____11198
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11198
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11195
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11192
                                                                     in
                                                                    (g,
                                                                    uu____11189,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11177
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
                                                                    let uu____11228
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11228
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
                                                                    let uu____11243
                                                                    =
                                                                    let uu____11246
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11246
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11243
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11252
                                                                    =
                                                                    let uu____11255
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11255
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11252
                                                                     in
                                                                    let uu____11260
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11260
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11276
                                                                    =
                                                                    let uu____11284
                                                                    =
                                                                    let uu____11285
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11286
                                                                    =
                                                                    let uu____11302
                                                                    =
                                                                    let uu____11303
                                                                    =
                                                                    let uu____11308
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11308)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11303
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11302)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11285
                                                                    uu____11286
                                                                     in
                                                                    let uu____11322
                                                                    =
                                                                    let uu____11323
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11323
                                                                     in
                                                                    (uu____11284,
                                                                    uu____11322,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11276
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11330
                                                                    =
                                                                    let uu____11338
                                                                    =
                                                                    let uu____11339
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11340
                                                                    =
                                                                    let uu____11351
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11351)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11339
                                                                    uu____11340
                                                                     in
                                                                    (uu____11338,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11330
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11365
                                                                    =
                                                                    let uu____11373
                                                                    =
                                                                    let uu____11374
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11375
                                                                    =
                                                                    let uu____11386
                                                                    =
                                                                    let uu____11387
                                                                    =
                                                                    let uu____11392
                                                                    =
                                                                    let uu____11393
                                                                    =
                                                                    let uu____11396
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11396
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11393
                                                                     in
                                                                    (gsapp,
                                                                    uu____11392)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11387
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11386)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11374
                                                                    uu____11375
                                                                     in
                                                                    (uu____11373,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11365
                                                                     in
                                                                    let uu____11410
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
                                                                    let uu____11422
                                                                    =
                                                                    let uu____11423
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11423
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11422
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____11425
                                                                    =
                                                                    let uu____11433
                                                                    =
                                                                    let uu____11434
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11435
                                                                    =
                                                                    let uu____11446
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11446)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11434
                                                                    uu____11435
                                                                     in
                                                                    (uu____11433,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11425
                                                                     in
                                                                    let uu____11459
                                                                    =
                                                                    let uu____11468
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11468
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11483
                                                                    =
                                                                    let uu____11486
                                                                    =
                                                                    let uu____11487
                                                                    =
                                                                    let uu____11495
                                                                    =
                                                                    let uu____11496
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11497
                                                                    =
                                                                    let uu____11508
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11508)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11496
                                                                    uu____11497
                                                                     in
                                                                    (uu____11495,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11487
                                                                     in
                                                                    [uu____11486]
                                                                     in
                                                                    (d3,
                                                                    uu____11483)
                                                                     in
                                                                    match uu____11459
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11410
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11565
                                                                    =
                                                                    let uu____11568
                                                                    =
                                                                    let uu____11571
                                                                    =
                                                                    let uu____11574
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11574
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11571
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11568
                                                                     in
                                                                    let uu____11581
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11565,
                                                                    uu____11581,
                                                                    env02))))))))))
                                      in
                                   let uu____11586 =
                                     let uu____11599 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11662  ->
                                          fun uu____11663  ->
                                            match (uu____11662, uu____11663)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11788 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11788 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11599
                                      in
                                   (match uu____11586 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11855 =
                                          let isDeclFun uu___1_11872 =
                                            match uu___1_11872 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11874 -> true
                                            | uu____11887 -> false  in
                                          let uu____11889 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11889
                                            (fun decls3  ->
                                               let uu____11919 =
                                                 FStar_List.fold_left
                                                   (fun uu____11950  ->
                                                      fun elt  ->
                                                        match uu____11950
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____11991 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____11991
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____12019
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____12019
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
                                                                    let uu___825_12057
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___825_12057.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___825_12057.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___825_12057.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____11919 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12089 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12089, elts, rest))
                                           in
                                        (match uu____11855 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12118 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12124  ->
                                        match uu___2_12124 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12127 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12135 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12135)))
                                in
                             if uu____12118
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___842_12157  ->
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
                   let uu____12196 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12196
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12215 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12215, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12271 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12271 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12277 = encode_sigelt' env se  in
      match uu____12277 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12289 =
                  let uu____12292 =
                    let uu____12293 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12293  in
                  [uu____12292]  in
                FStar_All.pipe_right uu____12289
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12298 ->
                let uu____12299 =
                  let uu____12302 =
                    let uu____12305 =
                      let uu____12306 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12306  in
                    [uu____12305]  in
                  FStar_All.pipe_right uu____12302
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12313 =
                  let uu____12316 =
                    let uu____12319 =
                      let uu____12322 =
                        let uu____12323 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12323  in
                      [uu____12322]  in
                    FStar_All.pipe_right uu____12319
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12316  in
                FStar_List.append uu____12299 uu____12313
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12337 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12337
       then
         let uu____12342 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12342
       else ());
      (let is_opaque_to_smt t =
         let uu____12354 =
           let uu____12355 = FStar_Syntax_Subst.compress t  in
           uu____12355.FStar_Syntax_Syntax.n  in
         match uu____12354 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12360)) -> s = "opaque_to_smt"
         | uu____12365 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12374 =
           let uu____12375 = FStar_Syntax_Subst.compress t  in
           uu____12375.FStar_Syntax_Syntax.n  in
         match uu____12374 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12380)) -> s = "uninterpreted_by_smt"
         | uu____12385 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12391 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12397 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12409 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12410 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12411 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12424 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12426 =
             let uu____12428 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12428  in
           if uu____12426
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12457 ->
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
                  let uu____12490 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____12490  in
                let uu____12491 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12491 with
                | (formals,uu____12511) ->
                    let arity = FStar_List.length formals  in
                    let uu____12535 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12535 with
                     | (aname,atok,env2) ->
                         let uu____12557 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____12557 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12573 =
                                  let uu____12574 =
                                    let uu____12586 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____12606  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12586,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12574
                                   in
                                [uu____12573;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____12623 =
                                let aux uu____12669 uu____12670 =
                                  match (uu____12669, uu____12670) with
                                  | ((bv,uu____12714),(env3,acc_sorts,acc))
                                      ->
                                      let uu____12746 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____12746 with
                                       | (xxsym,xx,env4) ->
                                           let uu____12769 =
                                             let uu____12772 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____12772 :: acc_sorts  in
                                           (env4, uu____12769, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____12623 with
                               | (uu____12804,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____12820 =
                                       let uu____12828 =
                                         let uu____12829 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12830 =
                                           let uu____12841 =
                                             let uu____12842 =
                                               let uu____12847 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____12847)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____12842
                                              in
                                           ([[app]], xs_sorts, uu____12841)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12829 uu____12830
                                          in
                                       (uu____12828,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12820
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____12862 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____12862
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____12865 =
                                       let uu____12873 =
                                         let uu____12874 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12875 =
                                           let uu____12886 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____12886)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12874 uu____12875
                                          in
                                       (uu____12873,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12865
                                      in
                                   let uu____12899 =
                                     let uu____12902 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____12902  in
                                   (env2, uu____12899))))
                 in
              let uu____12911 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____12911 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12937,uu____12938)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____12939 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____12939 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12961,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____12968 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_12974  ->
                       match uu___3_12974 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____12977 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____12983 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____12986 -> false))
                in
             Prims.op_Negation uu____12968  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____12996 =
                let uu____13001 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____13001 env fv t quals  in
              match uu____12996 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____13015 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____13015  in
                  let uu____13018 =
                    let uu____13019 =
                      let uu____13022 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____13022
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____13019  in
                  (uu____13018, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13032 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13032 with
            | (uvs,f1) ->
                let env1 =
                  let uu___979_13044 = env  in
                  let uu____13045 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___979_13044.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___979_13044.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___979_13044.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13045;
                    FStar_SMTEncoding_Env.warn =
                      (uu___979_13044.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___979_13044.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___979_13044.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___979_13044.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___979_13044.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___979_13044.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___979_13044.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____13047 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13047 with
                 | (f3,decls) ->
                     let g =
                       let uu____13061 =
                         let uu____13064 =
                           let uu____13065 =
                             let uu____13073 =
                               let uu____13074 =
                                 let uu____13076 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13076
                                  in
                               FStar_Pervasives_Native.Some uu____13074  in
                             let uu____13080 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13073, uu____13080)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13065  in
                         [uu____13064]  in
                       FStar_All.pipe_right uu____13061
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13089) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13103 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13125 =
                        let uu____13128 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13128.FStar_Syntax_Syntax.fv_name  in
                      uu____13125.FStar_Syntax_Syntax.v  in
                    let uu____13129 =
                      let uu____13131 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13131  in
                    if uu____13129
                    then
                      let val_decl =
                        let uu___996_13163 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___996_13163.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___996_13163.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___996_13163.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____13164 = encode_sigelt' env1 val_decl  in
                      match uu____13164 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13103 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13200,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13202;
                           FStar_Syntax_Syntax.lbtyp = uu____13203;
                           FStar_Syntax_Syntax.lbeff = uu____13204;
                           FStar_Syntax_Syntax.lbdef = uu____13205;
                           FStar_Syntax_Syntax.lbattrs = uu____13206;
                           FStar_Syntax_Syntax.lbpos = uu____13207;_}::[]),uu____13208)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13227 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____13227 with
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
                  let uu____13265 =
                    let uu____13268 =
                      let uu____13269 =
                        let uu____13277 =
                          let uu____13278 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13279 =
                            let uu____13290 =
                              let uu____13291 =
                                let uu____13296 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13296)  in
                              FStar_SMTEncoding_Util.mkEq uu____13291  in
                            ([[b2t_x]], [xx], uu____13290)  in
                          FStar_SMTEncoding_Term.mkForall uu____13278
                            uu____13279
                           in
                        (uu____13277,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13269  in
                    [uu____13268]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13265
                   in
                let uu____13334 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13334, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13337,uu____13338) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13348  ->
                   match uu___4_13348 with
                   | FStar_Syntax_Syntax.Discriminator uu____13350 -> true
                   | uu____13352 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13354,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13366 =
                      let uu____13368 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13368.FStar_Ident.idText  in
                    uu____13366 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13375  ->
                      match uu___5_13375 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13378 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13381) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13395  ->
                   match uu___6_13395 with
                   | FStar_Syntax_Syntax.Projector uu____13397 -> true
                   | uu____13403 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13407 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13407 with
            | FStar_Pervasives_Native.Some uu____13414 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1061_13416 = se  in
                  let uu____13417 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13417;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1061_13416.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1061_13416.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1061_13416.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13420) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1073_13441 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1073_13441.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1073_13441.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1073_13441.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1073_13441.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1073_13441.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13446) ->
           let uu____13455 = encode_sigelts env ses  in
           (match uu____13455 with
            | (g,env1) ->
                let uu____13466 =
                  FStar_List.fold_left
                    (fun uu____13490  ->
                       fun elt  ->
                         match uu____13490 with
                         | (g',inversions) ->
                             let uu____13518 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_13541  ->
                                       match uu___7_13541 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13543;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13544;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13545;_}
                                           -> false
                                       | uu____13552 -> true))
                                in
                             (match uu____13518 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1099_13577 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1099_13577.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1099_13577.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1099_13577.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13466 with
                 | (g',inversions) ->
                     let uu____13596 =
                       FStar_List.fold_left
                         (fun uu____13627  ->
                            fun elt  ->
                              match uu____13627 with
                              | (decls,elts,rest) ->
                                  let uu____13668 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_13677  ->
                                            match uu___8_13677 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____13679 -> true
                                            | uu____13692 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____13668
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____13715 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_13736  ->
                                               match uu___9_13736 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____13738 -> true
                                               | uu____13751 -> false))
                                        in
                                     match uu____13715 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1121_13782 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1121_13782.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1121_13782.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1121_13782.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____13596 with
                      | (decls,elts,rest) ->
                          let uu____13808 =
                            let uu____13809 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____13816 =
                              let uu____13819 =
                                let uu____13822 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____13822  in
                              FStar_List.append elts uu____13819  in
                            FStar_List.append uu____13809 uu____13816  in
                          (uu____13808, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____13833,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____13846 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____13846 with
             | (usubst,uvs) ->
                 let uu____13866 =
                   let uu____13873 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____13874 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____13875 =
                     let uu____13876 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____13876 k  in
                   (uu____13873, uu____13874, uu____13875)  in
                 (match uu____13866 with
                  | (env1,tps1,k1) ->
                      let uu____13889 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____13889 with
                       | (tps2,k2) ->
                           let uu____13897 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____13897 with
                            | (uu____13913,k3) ->
                                let uu____13935 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____13935 with
                                 | (tps3,env_tps,uu____13947,us) ->
                                     let u_k =
                                       let uu____13950 =
                                         let uu____13951 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____13952 =
                                           let uu____13957 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____13959 =
                                             let uu____13960 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____13960
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____13957 uu____13959
                                            in
                                         uu____13952
                                           FStar_Pervasives_Native.None
                                           uu____13951
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____13950 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____13978) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____13984,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____13987) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____13995,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____14002) ->
                                           let uu____14003 =
                                             let uu____14005 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14005
                                              in
                                           failwith uu____14003
                                       | (uu____14009,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____14010 =
                                             let uu____14012 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14012
                                              in
                                           failwith uu____14010
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14016,uu____14017) ->
                                           let uu____14026 =
                                             let uu____14028 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14028
                                              in
                                           failwith uu____14026
                                       | (uu____14032,FStar_Syntax_Syntax.U_unif
                                          uu____14033) ->
                                           let uu____14042 =
                                             let uu____14044 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14044
                                              in
                                           failwith uu____14042
                                       | uu____14048 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14061 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14061 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14079 = u_leq_u_k u_tp  in
                                       if uu____14079
                                       then true
                                       else
                                         (let uu____14086 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14086 with
                                          | (formals,uu____14103) ->
                                              let uu____14124 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14124 with
                                               | (uu____14134,uu____14135,uu____14136,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14147 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14147
             then
               let uu____14152 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14152
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14172  ->
                       match uu___10_14172 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14176 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14189 = c  in
                 match uu____14189 with
                 | (name,args,uu____14194,uu____14195,uu____14196) ->
                     let uu____14207 =
                       let uu____14208 =
                         let uu____14220 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14247  ->
                                   match uu____14247 with
                                   | (uu____14256,sort,uu____14258) -> sort))
                            in
                         (name, uu____14220,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14208  in
                     [uu____14207]
               else
                 (let uu____14269 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14269 c)
                in
             let inversion_axioms tapp vars =
               let uu____14287 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14295 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14295 FStar_Option.isNone))
                  in
               if uu____14287
               then []
               else
                 (let uu____14330 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14330 with
                  | (xxsym,xx) ->
                      let uu____14343 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14382  ->
                                fun l  ->
                                  match uu____14382 with
                                  | (out,decls) ->
                                      let uu____14402 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14402 with
                                       | (uu____14413,data_t) ->
                                           let uu____14415 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14415 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14459 =
                                                    let uu____14460 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14460.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14459 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14463,indices)
                                                      -> indices
                                                  | uu____14489 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14519  ->
                                                            match uu____14519
                                                            with
                                                            | (x,uu____14527)
                                                                ->
                                                                let uu____14532
                                                                  =
                                                                  let uu____14533
                                                                    =
                                                                    let uu____14541
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14541,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14533
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14532)
                                                       env)
                                                   in
                                                let uu____14546 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14546 with
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
                                                                  let uu____14581
                                                                    =
                                                                    let uu____14586
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____14586,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____14581)
                                                             vars indices1
                                                         else []  in
                                                       let uu____14589 =
                                                         let uu____14590 =
                                                           let uu____14595 =
                                                             let uu____14596
                                                               =
                                                               let uu____14601
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____14602
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____14601,
                                                                 uu____14602)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____14596
                                                              in
                                                           (out, uu____14595)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____14590
                                                          in
                                                       (uu____14589,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14343 with
                       | (data_ax,decls) ->
                           let uu____14617 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____14617 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____14634 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____14634 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____14641 =
                                    let uu____14649 =
                                      let uu____14650 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____14651 =
                                        let uu____14662 =
                                          let uu____14663 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____14665 =
                                            let uu____14668 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____14668 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____14663 uu____14665
                                           in
                                        let uu____14670 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____14662,
                                          uu____14670)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____14650 uu____14651
                                       in
                                    let uu____14679 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____14649,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____14679)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____14641
                                   in
                                let uu____14685 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____14685)))
                in
             let uu____14692 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____14714 ->
                     let uu____14715 =
                       let uu____14722 =
                         let uu____14723 =
                           let uu____14738 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____14738)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____14723  in
                       FStar_Syntax_Syntax.mk uu____14722  in
                     uu____14715 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____14692 with
             | (formals,res) ->
                 let uu____14778 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____14778 with
                  | (vars,guards,env',binder_decls,uu____14803) ->
                      let arity = FStar_List.length vars  in
                      let uu____14817 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____14817 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____14843 =
                               let uu____14851 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____14851)  in
                             FStar_SMTEncoding_Util.mkApp uu____14843  in
                           let uu____14857 =
                             let tname_decl =
                               let uu____14867 =
                                 let uu____14868 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____14887 =
                                             let uu____14889 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____14889
                                              in
                                           let uu____14891 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____14887, uu____14891, false)))
                                    in
                                 let uu____14895 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____14868,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____14895, false)
                                  in
                               constructor_or_logic_type_decl uu____14867  in
                             let uu____14903 =
                               match vars with
                               | [] ->
                                   let uu____14916 =
                                     let uu____14917 =
                                       let uu____14920 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _14926  ->
                                            FStar_Pervasives_Native.Some
                                              _14926) uu____14920
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____14917
                                      in
                                   ([], uu____14916)
                               | uu____14929 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____14939 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____14939
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____14955 =
                                       let uu____14963 =
                                         let uu____14964 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14965 =
                                           let uu____14981 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____14981)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____14964 uu____14965
                                          in
                                       (uu____14963,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____14955
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____14903 with
                             | (tok_decls,env2) ->
                                 let uu____15008 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____15008
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____14857 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____15036 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____15036 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____15058 =
                                            let uu____15059 =
                                              let uu____15067 =
                                                let uu____15068 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15068
                                                 in
                                              (uu____15067,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15059
                                             in
                                          [uu____15058]
                                        else []  in
                                      let uu____15076 =
                                        let uu____15079 =
                                          let uu____15082 =
                                            let uu____15085 =
                                              let uu____15086 =
                                                let uu____15094 =
                                                  let uu____15095 =
                                                    FStar_Ident.range_of_lid
                                                      t
                                                     in
                                                  let uu____15096 =
                                                    let uu____15107 =
                                                      FStar_SMTEncoding_Util.mkImp
                                                        (guard, k1)
                                                       in
                                                    ([[tapp]], vars,
                                                      uu____15107)
                                                     in
                                                  FStar_SMTEncoding_Term.mkForall
                                                    uu____15095 uu____15096
                                                   in
                                                (uu____15094,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15086
                                               in
                                            [uu____15085]  in
                                          FStar_List.append karr uu____15082
                                           in
                                        FStar_All.pipe_right uu____15079
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15076
                                   in
                                let aux =
                                  let uu____15126 =
                                    let uu____15129 =
                                      inversion_axioms tapp vars  in
                                    let uu____15132 =
                                      let uu____15135 =
                                        let uu____15138 =
                                          let uu____15139 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15139 env2 tapp
                                            vars
                                           in
                                        [uu____15138]  in
                                      FStar_All.pipe_right uu____15135
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15129 uu____15132
                                     in
                                  FStar_List.append kindingAx uu____15126  in
                                let g =
                                  let uu____15147 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15147
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15155,uu____15156,uu____15157,uu____15158,uu____15159)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15167,t,uu____15169,n_tps,uu____15171) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15182 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15182 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15230 =
                  FStar_SMTEncoding_Env.fresh_fvar
                    env.FStar_SMTEncoding_Env.current_module_name "f"
                    FStar_SMTEncoding_Term.Fuel_sort
                   in
                (match uu____15230 with
                 | (fuel_var,fuel_tm) ->
                     let s_fuel_tm =
                       FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])  in
                     let uu____15250 =
                       FStar_SMTEncoding_EncodeTerm.encode_binders
                         (FStar_Pervasives_Native.Some fuel_tm) formals env
                        in
                     (match uu____15250 with
                      | (vars,guards,env',binder_decls,names1) ->
                          let fields =
                            FStar_All.pipe_right names1
                              (FStar_List.mapi
                                 (fun n1  ->
                                    fun x  ->
                                      let projectible = true  in
                                      let uu____15329 =
                                        FStar_SMTEncoding_Env.mk_term_projector_name
                                          d x
                                         in
                                      (uu____15329,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        projectible)))
                             in
                          let dummy_var =
                            FStar_SMTEncoding_Term.mk_fv
                              ("@dummy", FStar_SMTEncoding_Term.dummy_sort)
                             in
                          let dummy_tm =
                            FStar_SMTEncoding_Term.mkFreeV dummy_var
                              FStar_Range.dummyRange
                             in
                          let uu____15337 =
                            match fields with
                            | [] when d.FStar_Ident.nsstr <> "Prims" ->
                                (true,
                                  [((Prims.op_Hat d.FStar_Ident.str "_0"),
                                     FStar_SMTEncoding_Term.dummy_sort,
                                     false)], [dummy_var])
                            | uu____15460 -> (false, fields, vars)  in
                          (match uu____15337 with
                           | (thunked,fields1,vars1) ->
                               let uu____15542 =
                                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                   env d arity thunked
                                  in
                               (match uu____15542 with
                                | (ddconstrsym,ddtok,env1) ->
                                    let ddtok_tm =
                                      match ddtok with
                                      | FStar_Pervasives_Native.Some ddtok1
                                          ->
                                          FStar_SMTEncoding_Util.mkApp
                                            (ddtok1, [])
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_SMTEncoding_Util.mkApp
                                            (ddconstrsym, [dummy_tm])
                                       in
                                    let datacons =
                                      let uu____15582 =
                                        FStar_Ident.range_of_lid d  in
                                      let uu____15583 =
                                        let uu____15584 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        (ddconstrsym, fields1,
                                          FStar_SMTEncoding_Term.Term_sort,
                                          uu____15584, true)
                                         in
                                      FStar_SMTEncoding_Term.constructor_to_decl
                                        uu____15582 uu____15583
                                       in
                                    let app =
                                      FStar_SMTEncoding_EncodeTerm.mk_Apply
                                        ddtok_tm vars1
                                       in
                                    let guard =
                                      FStar_SMTEncoding_Util.mk_and_l guards
                                       in
                                    let xvars =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars1
                                       in
                                    let dapp =
                                      FStar_SMTEncoding_Util.mkApp
                                        (ddconstrsym, xvars)
                                       in
                                    let uu____15609 =
                                      FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                        FStar_Pervasives_Native.None t1 env1
                                        ddtok_tm
                                       in
                                    (match uu____15609 with
                                     | (tok_typing,decls3) ->
                                         let tok_typing1 =
                                           match fields1 with
                                           | uu____15621::uu____15622 when
                                               Prims.op_Negation thunked ->
                                               let ff =
                                                 FStar_SMTEncoding_Term.mk_fv
                                                   ("ty",
                                                     FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               let f =
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                   ff
                                                  in
                                               let vtok_app_l =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   ddtok_tm [ff]
                                                  in
                                               let vtok_app_r =
                                                 let uu____15671 =
                                                   let uu____15672 =
                                                     let uu____15681 =
                                                       let uu____15687 =
                                                         FStar_Option.get
                                                           ddtok
                                                          in
                                                       (uu____15687,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_SMTEncoding_Term.mk_fv
                                                       uu____15681
                                                      in
                                                   [uu____15672]  in
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   f uu____15671
                                                  in
                                               let uu____15707 =
                                                 FStar_Ident.range_of_lid d
                                                  in
                                               let uu____15708 =
                                                 let uu____15719 =
                                                   FStar_SMTEncoding_Term.mk_NoHoist
                                                     f tok_typing
                                                    in
                                                 ([[vtok_app_l];
                                                  [vtok_app_r]], [ff],
                                                   uu____15719)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 uu____15707 uu____15708
                                           | uu____15746 ->
                                               let uu____15757 =
                                                 FStar_Ident.range_of_lid d
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 uu____15757
                                                 ([[dapp]], [dummy_var],
                                                   tok_typing)
                                            in
                                         let uu____15782 =
                                           FStar_SMTEncoding_EncodeTerm.encode_binders
                                             (FStar_Pervasives_Native.Some
                                                fuel_tm) formals env1
                                            in
                                         (match uu____15782 with
                                          | (vars',guards',env'',decls_formals,uu____15807)
                                              ->
                                              let vars'1 =
                                                if thunked
                                                then dummy_var :: vars'
                                                else vars'  in
                                              let uu____15844 =
                                                let xvars1 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars'1
                                                   in
                                                let dapp1 =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (ddconstrsym, xvars1)
                                                   in
                                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                  (FStar_Pervasives_Native.Some
                                                     fuel_tm) t_res env''
                                                  dapp1
                                                 in
                                              (match uu____15844 with
                                               | (ty_pred',decls_pred) ->
                                                   let guard' =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards'
                                                      in
                                                   let proxy_fresh =
                                                     match formals with
                                                     | uu____15876::uu____15877
                                                         when
                                                         Prims.op_Negation
                                                           thunked
                                                         ->
                                                         let uu____15898 =
                                                           let uu____15899 =
                                                             let uu____15905
                                                               =
                                                               FStar_Option.get
                                                                 ddtok
                                                                in
                                                             (uu____15905,
                                                               FStar_SMTEncoding_Term.Term_sort)
                                                              in
                                                           let uu____15909 =
                                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                               ()
                                                              in
                                                           FStar_SMTEncoding_Term.fresh_token
                                                             uu____15899
                                                             uu____15909
                                                            in
                                                         [uu____15898]
                                                     | uu____15911 -> []  in
                                                   let encode_elim
                                                     uu____15933 =
                                                     let uu____15934 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t_res
                                                        in
                                                     match uu____15934 with
                                                     | (head1,args) ->
                                                         let uu____15985 =
                                                           let uu____15986 =
                                                             FStar_Syntax_Subst.compress
                                                               head1
                                                              in
                                                           uu____15986.FStar_Syntax_Syntax.n
                                                            in
                                                         (match uu____15985
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uinst
                                                              ({
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Tm_fvar
                                                                   fv;
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____15998;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____15999;_},uu____16000)
                                                              ->
                                                              let encoded_head_fvb
                                                                =
                                                                FStar_SMTEncoding_Env.lookup_free_var_name
                                                                  env'
                                                                  fv.FStar_Syntax_Syntax.fv_name
                                                                 in
                                                              let uu____16006
                                                                =
                                                                FStar_SMTEncoding_EncodeTerm.encode_args
                                                                  args env'
                                                                 in
                                                              (match uu____16006
                                                               with
                                                               | (encoded_args,arg_decls)
                                                                   ->
                                                                   let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____16069
                                                                    ->
                                                                    let uu____16070
                                                                    =
                                                                    let uu____16076
                                                                    =
                                                                    let uu____16078
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16078
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16076)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16070
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16101
                                                                    =
                                                                    let uu____16103
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16103
                                                                     in
                                                                    if
                                                                    uu____16101
                                                                    then
                                                                    let uu____16125
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16125]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                   let uu____16128
                                                                    =
                                                                    let uu____16142
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____16199
                                                                     ->
                                                                    fun
                                                                    uu____16200
                                                                     ->
                                                                    match 
                                                                    (uu____16199,
                                                                    uu____16200)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16311
                                                                    =
                                                                    let uu____16319
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16319
                                                                     in
                                                                    (match uu____16311
                                                                    with
                                                                    | 
                                                                    (uu____16333,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16344
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16344
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16349
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16349
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____16142
                                                                     in
                                                                   (match uu____16128
                                                                    with
                                                                    | 
                                                                    (uu____16370,arg_vars,elim_eqns_or_guards,uu____16373)
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
                                                                    vars1  in
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
                                                                    let uu____16424
                                                                    =
                                                                    let uu____16432
                                                                    =
                                                                    let uu____16433
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16434
                                                                    =
                                                                    let uu____16445
                                                                    =
                                                                    let uu____16446
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16446
                                                                    (FStar_List.append
                                                                    vars1
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16472
                                                                    =
                                                                    let uu____16473
                                                                    =
                                                                    let uu____16478
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16478)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16473
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16445,
                                                                    uu____16472)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16433
                                                                    uu____16434
                                                                     in
                                                                    (uu____16432,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16424
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16495
                                                                    =
                                                                    let uu____16496
                                                                    =
                                                                    let uu____16502
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16502,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16496
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16495
                                                                     in
                                                                    let uu____16505
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16505
                                                                    then
                                                                    let x =
                                                                    let uu____16511
                                                                    =
                                                                    let uu____16517
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16517,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16511
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16522
                                                                    =
                                                                    let uu____16523
                                                                    =
                                                                    let uu____16531
                                                                    =
                                                                    let uu____16532
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16533
                                                                    =
                                                                    let uu____16544
                                                                    =
                                                                    let uu____16549
                                                                    =
                                                                    let uu____16552
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16552]
                                                                     in
                                                                    [uu____16549]
                                                                     in
                                                                    let uu____16557
                                                                    =
                                                                    let uu____16558
                                                                    =
                                                                    let uu____16563
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16565
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16563,
                                                                    uu____16565)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16558
                                                                     in
                                                                    (uu____16544,
                                                                    [x],
                                                                    uu____16557)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16532
                                                                    uu____16533
                                                                     in
                                                                    let uu____16586
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16531,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16586)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16523
                                                                     in
                                                                    [uu____16522]
                                                                    else
                                                                    if
                                                                    thunked
                                                                    then []
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16602
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars1
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____16625
                                                                    =
                                                                    let uu____16626
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16626
                                                                    dapp1  in
                                                                    [uu____16625])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16602
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16633
                                                                    =
                                                                    let uu____16634
                                                                    =
                                                                    let uu____16642
                                                                    =
                                                                    let uu____16643
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16644
                                                                    =
                                                                    let uu____16655
                                                                    =
                                                                    let uu____16656
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16656
                                                                    (FStar_List.append
                                                                    vars1
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16682
                                                                    =
                                                                    let uu____16683
                                                                    =
                                                                    let uu____16688
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16688)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16683
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16655,
                                                                    uu____16682)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16643
                                                                    uu____16644
                                                                     in
                                                                    (uu____16642,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16634
                                                                     in
                                                                    [uu____16633])
                                                                     in
                                                                    (arg_decls,
                                                                    (FStar_List.append
                                                                    [typing_inversion]
                                                                    subterm_ordering))))
                                                          | FStar_Syntax_Syntax.Tm_fvar
                                                              fv ->
                                                              let encoded_head_fvb
                                                                =
                                                                FStar_SMTEncoding_Env.lookup_free_var_name
                                                                  env'
                                                                  fv.FStar_Syntax_Syntax.fv_name
                                                                 in
                                                              let uu____16707
                                                                =
                                                                FStar_SMTEncoding_EncodeTerm.encode_args
                                                                  args env'
                                                                 in
                                                              (match uu____16707
                                                               with
                                                               | (encoded_args,arg_decls)
                                                                   ->
                                                                   let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____16770
                                                                    ->
                                                                    let uu____16771
                                                                    =
                                                                    let uu____16777
                                                                    =
                                                                    let uu____16779
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16779
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16777)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16771
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16802
                                                                    =
                                                                    let uu____16804
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16804
                                                                     in
                                                                    if
                                                                    uu____16802
                                                                    then
                                                                    let uu____16826
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16826]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                   let uu____16829
                                                                    =
                                                                    let uu____16843
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____16900
                                                                     ->
                                                                    fun
                                                                    uu____16901
                                                                     ->
                                                                    match 
                                                                    (uu____16900,
                                                                    uu____16901)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____17012
                                                                    =
                                                                    let uu____17020
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____17020
                                                                     in
                                                                    (match uu____17012
                                                                    with
                                                                    | 
                                                                    (uu____17034,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____17045
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____17045
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____17050
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____17050
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____16843
                                                                     in
                                                                   (match uu____16829
                                                                    with
                                                                    | 
                                                                    (uu____17071,arg_vars,elim_eqns_or_guards,uu____17074)
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
                                                                    vars1  in
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
                                                                    let uu____17125
                                                                    =
                                                                    let uu____17133
                                                                    =
                                                                    let uu____17134
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17135
                                                                    =
                                                                    let uu____17146
                                                                    =
                                                                    let uu____17147
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17147
                                                                    (FStar_List.append
                                                                    vars1
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17173
                                                                    =
                                                                    let uu____17174
                                                                    =
                                                                    let uu____17179
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____17179)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17174
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17146,
                                                                    uu____17173)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17134
                                                                    uu____17135
                                                                     in
                                                                    (uu____17133,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17125
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____17196
                                                                    =
                                                                    let uu____17197
                                                                    =
                                                                    let uu____17203
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____17203,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17197
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17196
                                                                     in
                                                                    let uu____17206
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____17206
                                                                    then
                                                                    let x =
                                                                    let uu____17212
                                                                    =
                                                                    let uu____17218
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____17218,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17212
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____17223
                                                                    =
                                                                    let uu____17224
                                                                    =
                                                                    let uu____17232
                                                                    =
                                                                    let uu____17233
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17234
                                                                    =
                                                                    let uu____17245
                                                                    =
                                                                    let uu____17250
                                                                    =
                                                                    let uu____17253
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____17253]
                                                                     in
                                                                    [uu____17250]
                                                                     in
                                                                    let uu____17258
                                                                    =
                                                                    let uu____17259
                                                                    =
                                                                    let uu____17264
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____17266
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____17264,
                                                                    uu____17266)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17259
                                                                     in
                                                                    (uu____17245,
                                                                    [x],
                                                                    uu____17258)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17233
                                                                    uu____17234
                                                                     in
                                                                    let uu____17287
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____17232,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____17287)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17224
                                                                     in
                                                                    [uu____17223]
                                                                    else
                                                                    if
                                                                    thunked
                                                                    then []
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____17303
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars1
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____17326
                                                                    =
                                                                    let uu____17327
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____17327
                                                                    dapp1  in
                                                                    [uu____17326])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17303
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____17334
                                                                    =
                                                                    let uu____17335
                                                                    =
                                                                    let uu____17343
                                                                    =
                                                                    let uu____17344
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17345
                                                                    =
                                                                    let uu____17356
                                                                    =
                                                                    let uu____17357
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17357
                                                                    (FStar_List.append
                                                                    vars1
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17383
                                                                    =
                                                                    let uu____17384
                                                                    =
                                                                    let uu____17389
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____17389)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17384
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17356,
                                                                    uu____17383)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17344
                                                                    uu____17345
                                                                     in
                                                                    (uu____17343,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17335
                                                                     in
                                                                    [uu____17334])
                                                                     in
                                                                    (arg_decls,
                                                                    (FStar_List.append
                                                                    [typing_inversion]
                                                                    subterm_ordering))))
                                                          | uu____17406 ->
                                                              ((let uu____17408
                                                                  =
                                                                  let uu____17414
                                                                    =
                                                                    let uu____17416
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    let uu____17418
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    head1  in
                                                                    FStar_Util.format2
                                                                    "Constructor %s builds an unexpected type %s\n"
                                                                    uu____17416
                                                                    uu____17418
                                                                     in
                                                                  (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                                    uu____17414)
                                                                   in
                                                                FStar_Errors.log_issue
                                                                  se.FStar_Syntax_Syntax.sigrng
                                                                  uu____17408);
                                                               ([], [])))
                                                      in
                                                   let uu____17426 =
                                                     encode_elim ()  in
                                                   (match uu____17426 with
                                                    | (decls2,elim) ->
                                                        let g =
                                                          let uu____17452 =
                                                            let uu____17455 =
                                                              let uu____17458
                                                                =
                                                                let uu____17461
                                                                  =
                                                                  match ddtok
                                                                  with
                                                                  | FStar_Pervasives_Native.None
                                                                     -> []
                                                                  | uu____17467
                                                                    ->
                                                                    let uu____17471
                                                                    =
                                                                    let uu____17474
                                                                    =
                                                                    let uu____17477
                                                                    =
                                                                    let uu____17478
                                                                    =
                                                                    let uu____17490
                                                                    =
                                                                    FStar_Option.get
                                                                    ddtok  in
                                                                    let uu____17493
                                                                    =
                                                                    let uu____17494
                                                                    =
                                                                    let uu____17496
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____17496
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____17494
                                                                     in
                                                                    (uu____17490,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____17493)
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____17478
                                                                     in
                                                                    [uu____17477]
                                                                     in
                                                                    FStar_List.append
                                                                    uu____17474
                                                                    proxy_fresh
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17471
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                   in
                                                                let uu____17507
                                                                  =
                                                                  let uu____17510
                                                                    =
                                                                    let uu____17513
                                                                    =
                                                                    let uu____17516
                                                                    =
                                                                    let uu____17519
                                                                    =
                                                                    let uu____17522
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddconstrsym))
                                                                     in
                                                                    [uu____17522]
                                                                     in
                                                                    let uu____17527
                                                                    =
                                                                    let uu____17530
                                                                    =
                                                                    if
                                                                    thunked
                                                                    then []
                                                                    else
                                                                    (let uu____17538
                                                                    =
                                                                    let uu____17539
                                                                    =
                                                                    let uu____17547
                                                                    =
                                                                    let uu____17548
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17549
                                                                    =
                                                                    let uu____17560
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars1,
                                                                    uu____17560)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17548
                                                                    uu____17549
                                                                     in
                                                                    (uu____17547,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17539
                                                                     in
                                                                    [uu____17538])
                                                                     in
                                                                    let uu____17573
                                                                    =
                                                                    let uu____17576
                                                                    =
                                                                    let uu____17579
                                                                    =
                                                                    let uu____17580
                                                                    =
                                                                    let uu____17588
                                                                    =
                                                                    let uu____17589
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17590
                                                                    =
                                                                    let uu____17601
                                                                    =
                                                                    let uu____17602
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17602
                                                                    vars'1
                                                                     in
                                                                    let uu____17620
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17601,
                                                                    uu____17620)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17589
                                                                    uu____17590
                                                                     in
                                                                    (uu____17588,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17580
                                                                     in
                                                                    [uu____17579]
                                                                     in
                                                                    FStar_List.append
                                                                    uu____17576
                                                                    elim  in
                                                                    FStar_List.append
                                                                    uu____17530
                                                                    uu____17573
                                                                     in
                                                                    FStar_List.append
                                                                    uu____17519
                                                                    uu____17527
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17516
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    decls_pred
                                                                    uu____17513
                                                                     in
                                                                  FStar_List.append
                                                                    decls_formals
                                                                    uu____17510
                                                                   in
                                                                FStar_List.append
                                                                  uu____17461
                                                                  uu____17507
                                                                 in
                                                              FStar_List.append
                                                                decls3
                                                                uu____17458
                                                               in
                                                            FStar_List.append
                                                              decls2
                                                              uu____17455
                                                             in
                                                          FStar_List.append
                                                            binder_decls
                                                            uu____17452
                                                           in
                                                        let uu____17637 =
                                                          let uu____17638 =
                                                            FStar_All.pipe_right
                                                              datacons
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            uu____17638 g
                                                           in
                                                        (uu____17637, env1)))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17672  ->
              fun se  ->
                match uu____17672 with
                | (g,env1) ->
                    let uu____17692 = encode_sigelt env1 se  in
                    (match uu____17692 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17760 =
        match uu____17760 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17797 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17805 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17805
                   then
                     let uu____17810 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17812 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17814 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17810 uu____17812 uu____17814
                   else ());
                  (let uu____17819 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17819 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17837 =
                         let uu____17845 =
                           let uu____17847 =
                             let uu____17849 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17849
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17847  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17845
                          in
                       (match uu____17837 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17869 = FStar_Options.log_queries ()
                                 in
                              if uu____17869
                              then
                                let uu____17872 =
                                  let uu____17874 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17876 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17878 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17874 uu____17876 uu____17878
                                   in
                                FStar_Pervasives_Native.Some uu____17872
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17894 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17904 =
                                let uu____17907 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17907  in
                              FStar_List.append uu____17894 uu____17904  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17919,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17939 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17939 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____17960 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____17960 with | (uu____17987,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____18040  ->
              match uu____18040 with
              | (l,uu____18049,uu____18050) ->
                  let uu____18053 =
                    let uu____18065 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____18065, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____18053))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____18098  ->
              match uu____18098 with
              | (l,uu____18109,uu____18110) ->
                  let uu____18113 =
                    let uu____18114 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _18117  -> FStar_SMTEncoding_Term.Echo _18117)
                      uu____18114
                     in
                  let uu____18118 =
                    let uu____18121 =
                      let uu____18122 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____18122  in
                    [uu____18121]  in
                  uu____18113 :: uu____18118))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____18140 =
      let uu____18143 =
        let uu____18144 = FStar_Util.psmap_empty ()  in
        let uu____18159 =
          let uu____18168 = FStar_Util.psmap_empty ()  in (uu____18168, [])
           in
        let uu____18175 =
          let uu____18177 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____18177 FStar_Ident.string_of_lid  in
        let uu____18179 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____18144;
          FStar_SMTEncoding_Env.fvar_bindings = uu____18159;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____18175;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____18179
        }  in
      [uu____18143]  in
    FStar_ST.op_Colon_Equals last_env uu____18140
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____18223 = FStar_ST.op_Bang last_env  in
      match uu____18223 with
      | [] -> failwith "No env; call init first!"
      | e::uu____18251 ->
          let uu___1564_18254 = e  in
          let uu____18255 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1564_18254.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1564_18254.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1564_18254.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1564_18254.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1564_18254.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1564_18254.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1564_18254.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____18255;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1564_18254.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1564_18254.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____18263 = FStar_ST.op_Bang last_env  in
    match uu____18263 with
    | [] -> failwith "Empty env stack"
    | uu____18290::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____18322  ->
    let uu____18323 = FStar_ST.op_Bang last_env  in
    match uu____18323 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____18383  ->
    let uu____18384 = FStar_ST.op_Bang last_env  in
    match uu____18384 with
    | [] -> failwith "Popping an empty stack"
    | uu____18411::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____18448  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____18501  ->
         let uu____18502 = snapshot_env ()  in
         match uu____18502 with
         | (env_depth,()) ->
             let uu____18524 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____18524 with
              | (varops_depth,()) ->
                  let uu____18546 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____18546 with
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
        (fun uu____18604  ->
           let uu____18605 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18605 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18700 = snapshot msg  in () 
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
        | (uu____18746::uu____18747,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1625_18755 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1625_18755.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1625_18755.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1625_18755.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18756 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1631_18783 = elt  in
        let uu____18784 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1631_18783.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1631_18783.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18784;
          FStar_SMTEncoding_Term.a_names =
            (uu___1631_18783.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18804 =
        let uu____18807 =
          let uu____18808 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18808  in
        let uu____18809 = open_fact_db_tags env  in uu____18807 ::
          uu____18809
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18804
  
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
      let uu____18836 = encode_sigelt env se  in
      match uu____18836 with
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
                (let uu____18882 =
                   let uu____18885 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18885
                    in
                 match uu____18882 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18900 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18900
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18930 = FStar_Options.log_queries ()  in
        if uu____18930
        then
          let uu____18935 =
            let uu____18936 =
              let uu____18938 =
                let uu____18940 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18940 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18938  in
            FStar_SMTEncoding_Term.Caption uu____18936  in
          uu____18935 :: decls
        else decls  in
      (let uu____18959 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18959
       then
         let uu____18962 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18962
       else ());
      (let env =
         let uu____18968 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18968 tcenv  in
       let uu____18969 = encode_top_level_facts env se  in
       match uu____18969 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18983 =
               let uu____18986 =
                 let uu____18989 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18989
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18986  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18983)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____19022 = FStar_Options.log_queries ()  in
          if uu____19022
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1669_19042 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1669_19042.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1669_19042.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1669_19042.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1669_19042.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1669_19042.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1669_19042.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1669_19042.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1669_19042.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1669_19042.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1669_19042.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____19047 =
             let uu____19050 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____19050
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____19047  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____19070 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____19070
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
          (let uu____19094 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____19094
           then
             let uu____19097 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____19097
           else ());
          (let env =
             let uu____19105 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____19105
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____19144  ->
                     fun se  ->
                       match uu____19144 with
                       | (g,env2) ->
                           let uu____19164 = encode_top_level_facts env2 se
                              in
                           (match uu____19164 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____19187 =
             encode_signature
               (let uu___1692_19196 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1692_19196.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1692_19196.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1692_19196.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1692_19196.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1692_19196.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1692_19196.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1692_19196.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1692_19196.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1692_19196.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1692_19196.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____19187 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19212 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19212
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____19218 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____19218))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____19246  ->
        match uu____19246 with
        | (decls,fvbs) ->
            ((let uu____19260 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____19260
              then ()
              else
                (let uu____19265 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19265
                 then
                   let uu____19268 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____19268
                 else ()));
             (let env =
                let uu____19276 = get_env name tcenv  in
                FStar_All.pipe_right uu____19276
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____19278 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____19278
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____19292 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____19292
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
        (let uu____19354 =
           let uu____19356 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____19356.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____19354);
        (let env =
           let uu____19358 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____19358 tcenv  in
         let uu____19359 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____19398 = aux rest  in
                 (match uu____19398 with
                  | (out,rest1) ->
                      let t =
                        let uu____19426 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____19426 with
                        | FStar_Pervasives_Native.Some uu____19429 ->
                            let uu____19430 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____19430
                              x.FStar_Syntax_Syntax.sort
                        | uu____19431 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____19435 =
                        let uu____19438 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1733_19441 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1733_19441.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1733_19441.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____19438 :: out  in
                      (uu____19435, rest1))
             | uu____19446 -> ([], bindings)  in
           let uu____19453 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____19453 with
           | (closing,bindings) ->
               let uu____19480 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____19480, bindings)
            in
         match uu____19359 with
         | (q1,bindings) ->
             let uu____19511 = encode_env_bindings env bindings  in
             (match uu____19511 with
              | (env_decls,env1) ->
                  ((let uu____19533 =
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
                    if uu____19533
                    then
                      let uu____19540 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____19540
                    else ());
                   (let uu____19545 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____19545 with
                    | (phi,qdecls) ->
                        let uu____19566 =
                          let uu____19571 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19571 phi
                           in
                        (match uu____19566 with
                         | (labels,phi1) ->
                             let uu____19588 = encode_labels labels  in
                             (match uu____19588 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19624 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19624
                                    then
                                      let uu____19629 =
                                        let uu____19630 =
                                          let uu____19632 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____19632
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19630
                                         in
                                      [uu____19629]
                                    else []  in
                                  let query_prelude =
                                    let uu____19640 =
                                      let uu____19641 =
                                        let uu____19642 =
                                          let uu____19645 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19652 =
                                            let uu____19655 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19655
                                             in
                                          FStar_List.append uu____19645
                                            uu____19652
                                           in
                                        FStar_List.append env_decls
                                          uu____19642
                                         in
                                      FStar_All.pipe_right uu____19641
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19640
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19665 =
                                      let uu____19673 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19674 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19673,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19674)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19665
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
  