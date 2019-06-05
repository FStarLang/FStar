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
                                       FStar_Pervasives_Native.None p env'
                                      in
                                   (match uu____7476 with
                                    | (g,ds) ->
                                        let uu____7490 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7490,
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
                                  let should_thunk uu____7513 =
                                    let is_type1 t =
                                      let uu____7521 =
                                        let uu____7522 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7522.FStar_Syntax_Syntax.n  in
                                      match uu____7521 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7526 -> true
                                      | uu____7528 -> false  in
                                    let is_squash1 t =
                                      let uu____7537 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____7537 with
                                      | (head1,uu____7556) ->
                                          let uu____7581 =
                                            let uu____7582 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____7582.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7581 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____7587;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____7588;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____7590;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____7591;_};_},uu____7592)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____7600 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____7605 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____7605))
                                       &&
                                       (let uu____7611 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____7611))
                                      &&
                                      (let uu____7614 = is_type1 t_norm  in
                                       Prims.op_Negation uu____7614)
                                     in
                                  let uu____7616 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____7675 -> (false, vars)  in
                                  (match uu____7616 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____7725 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____7725 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____7757 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____7766 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____7766
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
                                                              let uu____7921
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____7921
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _7925  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _7925)
                                                              uu____7920
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____7917
                                                           in
                                                        (uu____7906,
                                                          uu____7916)
                                                    | uu____7928 when thunked
                                                        -> (decls2, env1)
                                                    | uu____7941 ->
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
                                                          let uu____7965 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____7966 =
                                                            let uu____7977 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____7977)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____7965
                                                            uu____7966
                                                           in
                                                        let name_tok_corr =
                                                          let uu____7987 =
                                                            let uu____7995 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____7995,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7987
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
                                                            let uu____8006 =
                                                              let uu____8007
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8007]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8006
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8034 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8035 =
                                                              let uu____8046
                                                                =
                                                                let uu____8047
                                                                  =
                                                                  let uu____8052
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8053
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8052,
                                                                    uu____8053)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8047
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8046)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8034
                                                              uu____8035
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8082 =
                                                          let uu____8085 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8085
                                                           in
                                                        (uu____8082, env1)
                                                     in
                                                  (match uu____7880 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8106 =
                                                         let uu____8109 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8109
                                                           tok_decl
                                                          in
                                                       (uu____8106, env2))
                                               in
                                            (match uu____7823 with
                                             | (decls2,env2) ->
                                                 let uu____8128 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8138 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8138 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8153 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8153, decls)
                                                    in
                                                 (match uu____8128 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8168 =
                                                          let uu____8176 =
                                                            let uu____8177 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8178 =
                                                              let uu____8189
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8189)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8177
                                                              uu____8178
                                                             in
                                                          (uu____8176,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8168
                                                         in
                                                      let freshness =
                                                        let uu____8205 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8205
                                                        then
                                                          let uu____8213 =
                                                            let uu____8214 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8215 =
                                                              let uu____8228
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8235
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8228,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8235)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8214
                                                              uu____8215
                                                             in
                                                          let uu____8241 =
                                                            let uu____8244 =
                                                              let uu____8245
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8245
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8244]  in
                                                          uu____8213 ::
                                                            uu____8241
                                                        else []  in
                                                      let g =
                                                        let uu____8251 =
                                                          let uu____8254 =
                                                            let uu____8257 =
                                                              let uu____8260
                                                                =
                                                                let uu____8263
                                                                  =
                                                                  let uu____8266
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8266
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8263
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8260
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8257
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8254
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8251
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
          let uu____8306 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8306 with
          | FStar_Pervasives_Native.None  ->
              let uu____8317 = encode_free_var false env x t t_norm []  in
              (match uu____8317 with
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
            let uu____8380 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8380 with
            | (decls,env1) ->
                let uu____8391 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8391
                then
                  let uu____8398 =
                    let uu____8399 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8399  in
                  (uu____8398, env1)
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
             (fun uu____8455  ->
                fun lb  ->
                  match uu____8455 with
                  | (decls,env1) ->
                      let uu____8475 =
                        let uu____8480 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8480
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8475 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8509 = FStar_Syntax_Util.head_and_args t  in
    match uu____8509 with
    | (hd1,args) ->
        let uu____8553 =
          let uu____8554 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8554.FStar_Syntax_Syntax.n  in
        (match uu____8553 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8560,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____8584 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____8595 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___474_8603 = en  in
    let uu____8604 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___474_8603.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___474_8603.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___474_8603.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___474_8603.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___474_8603.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___474_8603.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___474_8603.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___474_8603.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___474_8603.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___474_8603.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____8604
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____8634  ->
      fun quals  ->
        match uu____8634 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8739 = FStar_Util.first_N nbinders formals  in
              match uu____8739 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____8836  ->
                         fun uu____8837  ->
                           match (uu____8836, uu____8837) with
                           | ((formal,uu____8863),(binder,uu____8865)) ->
                               let uu____8886 =
                                 let uu____8893 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____8893)  in
                               FStar_Syntax_Syntax.NT uu____8886) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____8907 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8948  ->
                              match uu____8948 with
                              | (x,i) ->
                                  let uu____8967 =
                                    let uu___500_8968 = x  in
                                    let uu____8969 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___500_8968.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___500_8968.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8969
                                    }  in
                                  (uu____8967, i)))
                       in
                    FStar_All.pipe_right uu____8907
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____8993 =
                      let uu____8998 = FStar_Syntax_Subst.compress body  in
                      let uu____8999 =
                        let uu____9000 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9000
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____8998 uu____8999
                       in
                    uu____8993 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___507_9049 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___507_9049.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___507_9049.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___507_9049.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___507_9049.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___507_9049.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___507_9049.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___507_9049.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___507_9049.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___507_9049.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___507_9049.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___507_9049.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___507_9049.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___507_9049.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___507_9049.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___507_9049.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___507_9049.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___507_9049.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___507_9049.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___507_9049.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___507_9049.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___507_9049.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___507_9049.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___507_9049.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___507_9049.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___507_9049.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___507_9049.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___507_9049.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___507_9049.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___507_9049.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___507_9049.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___507_9049.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___507_9049.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___507_9049.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___507_9049.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___507_9049.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___507_9049.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___507_9049.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___507_9049.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___507_9049.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___507_9049.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___507_9049.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___507_9049.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____9121  ->
                       fun uu____9122  ->
                         match (uu____9121, uu____9122) with
                         | ((x,uu____9148),(b,uu____9150)) ->
                             let uu____9171 =
                               let uu____9178 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9178)  in
                             FStar_Syntax_Syntax.NT uu____9171) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9203 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9203
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9232 ->
                    let uu____9239 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9239
                | uu____9240 when Prims.op_Negation norm1 ->
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
                | uu____9243 ->
                    let uu____9244 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9244)
                 in
              let aux t1 e1 =
                let uu____9286 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9286 with
                | (binders,body,lopt) ->
                    let uu____9318 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9334 -> arrow_formals_comp_norm false t1  in
                    (match uu____9318 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9368 =
                           if nformals < nbinders
                           then
                             let uu____9402 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9402 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9482 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9482)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9512 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9512 with
                                | (binders1,body1) ->
                                    let uu____9565 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____9565))
                             else
                               (let uu____9578 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____9578))
                            in
                         (match uu____9368 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____9638 = aux t e  in
              match uu____9638 with
              | (binders,body,comp) ->
                  let uu____9684 =
                    let uu____9695 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____9695
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____9710 = aux comp1 body1  in
                      match uu____9710 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____9684 with
                   | (binders1,body1,comp1) ->
                       let uu____9793 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____9793, comp1))
               in
            (try
               (fun uu___577_9820  ->
                  match () with
                  | () ->
                      let uu____9827 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9827
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9843 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9906  ->
                                   fun lb  ->
                                     match uu____9906 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9961 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9961
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9967 =
                                             let uu____9976 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9976
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9967 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9843 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10117;
                                    FStar_Syntax_Syntax.lbeff = uu____10118;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10120;
                                    FStar_Syntax_Syntax.lbpos = uu____10121;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10145 =
                                     let uu____10152 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10152 with
                                     | (tcenv',uu____10168,e_t) ->
                                         let uu____10174 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10185 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10174 with
                                          | (e1,t_norm1) ->
                                              ((let uu___640_10202 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___640_10202.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10145 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10212 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10212 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10232 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10232
                                               then
                                                 let uu____10237 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10240 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10237 uu____10240
                                               else ());
                                              (let uu____10245 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10245 with
                                               | (vars,_guards,env'1,binder_decls,uu____10272)
                                                   ->
                                                   let uu____10285 =
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
                                                         let uu____10302 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10302
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10324 =
                                                          let uu____10325 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10326 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10325 fvb
                                                            uu____10326
                                                           in
                                                        (vars, uu____10324))
                                                      in
                                                   (match uu____10285 with
                                                    | (vars1,app) ->
                                                        let uu____10337 =
                                                          let is_logical =
                                                            let uu____10350 =
                                                              let uu____10351
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10351.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10350
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10357 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10361 =
                                                              let uu____10362
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10362
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10361
                                                              (fun lid  ->
                                                                 let uu____10371
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10371
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10372 =
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
                                                          if uu____10372
                                                          then
                                                            let uu____10388 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10389 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                FStar_Pervasives_Native.None
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10388,
                                                              uu____10389)
                                                          else
                                                            (let uu____10401
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10401))
                                                           in
                                                        (match uu____10337
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
                                                                    FStar_Pervasives_Native.None
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11074
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11088
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11088,
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
                                                                    let uu____11109
                                                                    =
                                                                    let uu____11121
                                                                    =
                                                                    let uu____11124
                                                                    =
                                                                    let uu____11127
                                                                    =
                                                                    let uu____11130
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11130
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11127
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11124
                                                                     in
                                                                    (g,
                                                                    uu____11121,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11109
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
                                                                    let uu____11160
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11160
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
                                                                    let uu____11175
                                                                    =
                                                                    let uu____11178
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11178
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11175
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11184
                                                                    =
                                                                    let uu____11187
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11187
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11184
                                                                     in
                                                                    let uu____11192
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11192
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11208
                                                                    =
                                                                    let uu____11216
                                                                    =
                                                                    let uu____11217
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11218
                                                                    =
                                                                    let uu____11234
                                                                    =
                                                                    let uu____11235
                                                                    =
                                                                    let uu____11240
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11240)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11235
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11234)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11217
                                                                    uu____11218
                                                                     in
                                                                    let uu____11254
                                                                    =
                                                                    let uu____11255
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11255
                                                                     in
                                                                    (uu____11216,
                                                                    uu____11254,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11208
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11262
                                                                    =
                                                                    let uu____11270
                                                                    =
                                                                    let uu____11271
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11272
                                                                    =
                                                                    let uu____11283
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11283)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11271
                                                                    uu____11272
                                                                     in
                                                                    (uu____11270,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11262
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11297
                                                                    =
                                                                    let uu____11305
                                                                    =
                                                                    let uu____11306
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11307
                                                                    =
                                                                    let uu____11318
                                                                    =
                                                                    let uu____11319
                                                                    =
                                                                    let uu____11324
                                                                    =
                                                                    let uu____11325
                                                                    =
                                                                    let uu____11328
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11328
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11325
                                                                     in
                                                                    (gsapp,
                                                                    uu____11324)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11319
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11318)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11306
                                                                    uu____11307
                                                                     in
                                                                    (uu____11305,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11297
                                                                     in
                                                                    let uu____11342
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
                                                                    let uu____11354
                                                                    =
                                                                    let uu____11355
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11355
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11354
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____11357
                                                                    =
                                                                    let uu____11365
                                                                    =
                                                                    let uu____11366
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11367
                                                                    =
                                                                    let uu____11378
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11378)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11366
                                                                    uu____11367
                                                                     in
                                                                    (uu____11365,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11357
                                                                     in
                                                                    let uu____11391
                                                                    =
                                                                    let uu____11400
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11400
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11415
                                                                    =
                                                                    let uu____11418
                                                                    =
                                                                    let uu____11419
                                                                    =
                                                                    let uu____11427
                                                                    =
                                                                    let uu____11428
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11429
                                                                    =
                                                                    let uu____11440
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11440)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11428
                                                                    uu____11429
                                                                     in
                                                                    (uu____11427,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11419
                                                                     in
                                                                    [uu____11418]
                                                                     in
                                                                    (d3,
                                                                    uu____11415)
                                                                     in
                                                                    match uu____11391
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11342
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11497
                                                                    =
                                                                    let uu____11500
                                                                    =
                                                                    let uu____11503
                                                                    =
                                                                    let uu____11506
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11506
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11503
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11500
                                                                     in
                                                                    let uu____11513
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11497,
                                                                    uu____11513,
                                                                    env02))))))))))
                                      in
                                   let uu____11518 =
                                     let uu____11531 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11594  ->
                                          fun uu____11595  ->
                                            match (uu____11594, uu____11595)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11720 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11720 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11531
                                      in
                                   (match uu____11518 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11787 =
                                          let isDeclFun uu___1_11804 =
                                            match uu___1_11804 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11806 -> true
                                            | uu____11819 -> false  in
                                          let uu____11821 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11821
                                            (fun decls3  ->
                                               let uu____11851 =
                                                 FStar_List.fold_left
                                                   (fun uu____11882  ->
                                                      fun elt  ->
                                                        match uu____11882
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____11923 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____11923
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____11951
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____11951
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
                                                                    let uu___820_11989
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___820_11989.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___820_11989.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___820_11989.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____11851 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12021 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12021, elts, rest))
                                           in
                                        (match uu____11787 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12050 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12056  ->
                                        match uu___2_12056 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12059 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12067 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12067)))
                                in
                             if uu____12050
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___837_12089  ->
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
                   let uu____12128 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12128
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12147 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12147, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12203 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12203 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12209 = encode_sigelt' env se  in
      match uu____12209 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12221 =
                  let uu____12224 =
                    let uu____12225 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12225  in
                  [uu____12224]  in
                FStar_All.pipe_right uu____12221
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12230 ->
                let uu____12231 =
                  let uu____12234 =
                    let uu____12237 =
                      let uu____12238 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12238  in
                    [uu____12237]  in
                  FStar_All.pipe_right uu____12234
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12245 =
                  let uu____12248 =
                    let uu____12251 =
                      let uu____12254 =
                        let uu____12255 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12255  in
                      [uu____12254]  in
                    FStar_All.pipe_right uu____12251
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12248  in
                FStar_List.append uu____12231 uu____12245
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12269 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12269
       then
         let uu____12274 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12274
       else ());
      (let is_opaque_to_smt t =
         let uu____12286 =
           let uu____12287 = FStar_Syntax_Subst.compress t  in
           uu____12287.FStar_Syntax_Syntax.n  in
         match uu____12286 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12292)) -> s = "opaque_to_smt"
         | uu____12297 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12306 =
           let uu____12307 = FStar_Syntax_Subst.compress t  in
           uu____12307.FStar_Syntax_Syntax.n  in
         match uu____12306 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12312)) -> s = "uninterpreted_by_smt"
         | uu____12317 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12323 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12329 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12341 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12342 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12343 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12356 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12358 =
             let uu____12360 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12360  in
           if uu____12358
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12389 ->
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
                  let uu____12422 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____12422  in
                let uu____12423 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12423 with
                | (formals,uu____12443) ->
                    let arity = FStar_List.length formals  in
                    let uu____12467 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12467 with
                     | (aname,atok,env2) ->
                         let uu____12489 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____12489 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12505 =
                                  let uu____12506 =
                                    let uu____12518 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____12538  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12518,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12506
                                   in
                                [uu____12505;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____12555 =
                                let aux uu____12601 uu____12602 =
                                  match (uu____12601, uu____12602) with
                                  | ((bv,uu____12646),(env3,acc_sorts,acc))
                                      ->
                                      let uu____12678 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____12678 with
                                       | (xxsym,xx,env4) ->
                                           let uu____12701 =
                                             let uu____12704 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____12704 :: acc_sorts  in
                                           (env4, uu____12701, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____12555 with
                               | (uu____12736,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____12752 =
                                       let uu____12760 =
                                         let uu____12761 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12762 =
                                           let uu____12773 =
                                             let uu____12774 =
                                               let uu____12779 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____12779)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____12774
                                              in
                                           ([[app]], xs_sorts, uu____12773)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12761 uu____12762
                                          in
                                       (uu____12760,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12752
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____12794 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____12794
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____12797 =
                                       let uu____12805 =
                                         let uu____12806 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12807 =
                                           let uu____12818 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____12818)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12806 uu____12807
                                          in
                                       (uu____12805,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12797
                                      in
                                   let uu____12831 =
                                     let uu____12834 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____12834  in
                                   (env2, uu____12831))))
                 in
              let uu____12843 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____12843 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12869,uu____12870)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____12871 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____12871 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12893,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____12900 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_12906  ->
                       match uu___3_12906 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____12909 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____12915 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____12918 -> false))
                in
             Prims.op_Negation uu____12900  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____12928 =
                let uu____12933 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____12933 env fv t quals  in
              match uu____12928 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____12947 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____12947  in
                  let uu____12950 =
                    let uu____12951 =
                      let uu____12954 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____12954
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____12951  in
                  (uu____12950, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____12964 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____12964 with
            | (uvs,f1) ->
                let env1 =
                  let uu___974_12976 = env  in
                  let uu____12977 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___974_12976.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___974_12976.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___974_12976.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____12977;
                    FStar_SMTEncoding_Env.warn =
                      (uu___974_12976.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___974_12976.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___974_12976.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___974_12976.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___974_12976.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___974_12976.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___974_12976.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____12979 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula
                    FStar_Pervasives_Native.None f2 env1
                   in
                (match uu____12979 with
                 | (f3,decls) ->
                     let g =
                       let uu____12994 =
                         let uu____12997 =
                           let uu____12998 =
                             let uu____13006 =
                               let uu____13007 =
                                 let uu____13009 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13009
                                  in
                               FStar_Pervasives_Native.Some uu____13007  in
                             let uu____13013 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13006, uu____13013)  in
                           FStar_SMTEncoding_Util.mkAssume uu____12998  in
                         [uu____12997]  in
                       FStar_All.pipe_right uu____12994
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13022) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13036 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13058 =
                        let uu____13061 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13061.FStar_Syntax_Syntax.fv_name  in
                      uu____13058.FStar_Syntax_Syntax.v  in
                    let uu____13062 =
                      let uu____13064 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13064  in
                    if uu____13062
                    then
                      let val_decl =
                        let uu___991_13096 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___991_13096.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___991_13096.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___991_13096.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____13097 = encode_sigelt' env1 val_decl  in
                      match uu____13097 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13036 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13133,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13135;
                           FStar_Syntax_Syntax.lbtyp = uu____13136;
                           FStar_Syntax_Syntax.lbeff = uu____13137;
                           FStar_Syntax_Syntax.lbdef = uu____13138;
                           FStar_Syntax_Syntax.lbattrs = uu____13139;
                           FStar_Syntax_Syntax.lbpos = uu____13140;_}::[]),uu____13141)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13160 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____13160 with
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
                  let uu____13198 =
                    let uu____13201 =
                      let uu____13202 =
                        let uu____13210 =
                          let uu____13211 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13212 =
                            let uu____13223 =
                              let uu____13224 =
                                let uu____13229 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13229)  in
                              FStar_SMTEncoding_Util.mkEq uu____13224  in
                            ([[b2t_x]], [xx], uu____13223)  in
                          FStar_SMTEncoding_Term.mkForall uu____13211
                            uu____13212
                           in
                        (uu____13210,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13202  in
                    [uu____13201]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13198
                   in
                let uu____13267 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13267, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13270,uu____13271) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13281  ->
                   match uu___4_13281 with
                   | FStar_Syntax_Syntax.Discriminator uu____13283 -> true
                   | uu____13285 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13287,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13299 =
                      let uu____13301 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13301.FStar_Ident.idText  in
                    uu____13299 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13308  ->
                      match uu___5_13308 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13311 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13314) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13328  ->
                   match uu___6_13328 with
                   | FStar_Syntax_Syntax.Projector uu____13330 -> true
                   | uu____13336 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13340 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13340 with
            | FStar_Pervasives_Native.Some uu____13347 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1056_13349 = se  in
                  let uu____13350 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13350;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1056_13349.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1056_13349.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1056_13349.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13353) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1068_13374 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1068_13374.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1068_13374.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1068_13374.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1068_13374.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1068_13374.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13379) ->
           let uu____13388 = encode_sigelts env ses  in
           (match uu____13388 with
            | (g,env1) ->
                let uu____13399 =
                  FStar_List.fold_left
                    (fun uu____13423  ->
                       fun elt  ->
                         match uu____13423 with
                         | (g',inversions) ->
                             let uu____13451 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_13474  ->
                                       match uu___7_13474 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13476;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13477;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13478;_}
                                           -> false
                                       | uu____13485 -> true))
                                in
                             (match uu____13451 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1094_13510 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1094_13510.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1094_13510.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1094_13510.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13399 with
                 | (g',inversions) ->
                     let uu____13529 =
                       FStar_List.fold_left
                         (fun uu____13560  ->
                            fun elt  ->
                              match uu____13560 with
                              | (decls,elts,rest) ->
                                  let uu____13601 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_13610  ->
                                            match uu___8_13610 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____13612 -> true
                                            | uu____13625 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____13601
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____13648 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_13669  ->
                                               match uu___9_13669 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____13671 -> true
                                               | uu____13684 -> false))
                                        in
                                     match uu____13648 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1116_13715 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1116_13715.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1116_13715.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1116_13715.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____13529 with
                      | (decls,elts,rest) ->
                          let uu____13741 =
                            let uu____13742 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____13749 =
                              let uu____13752 =
                                let uu____13755 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____13755  in
                              FStar_List.append elts uu____13752  in
                            FStar_List.append uu____13742 uu____13749  in
                          (uu____13741, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____13766,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____13779 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____13779 with
             | (usubst,uvs) ->
                 let uu____13799 =
                   let uu____13806 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____13807 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____13808 =
                     let uu____13809 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____13809 k  in
                   (uu____13806, uu____13807, uu____13808)  in
                 (match uu____13799 with
                  | (env1,tps1,k1) ->
                      let uu____13822 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____13822 with
                       | (tps2,k2) ->
                           let uu____13830 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____13830 with
                            | (uu____13846,k3) ->
                                let uu____13868 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____13868 with
                                 | (tps3,env_tps,uu____13880,us) ->
                                     let u_k =
                                       let uu____13883 =
                                         let uu____13884 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____13885 =
                                           let uu____13890 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____13892 =
                                             let uu____13893 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____13893
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____13890 uu____13892
                                            in
                                         uu____13885
                                           FStar_Pervasives_Native.None
                                           uu____13884
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____13883 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____13911) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____13917,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____13920) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____13928,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____13935) ->
                                           let uu____13936 =
                                             let uu____13938 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13938
                                              in
                                           failwith uu____13936
                                       | (uu____13942,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____13943 =
                                             let uu____13945 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13945
                                              in
                                           failwith uu____13943
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____13949,uu____13950) ->
                                           let uu____13959 =
                                             let uu____13961 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13961
                                              in
                                           failwith uu____13959
                                       | (uu____13965,FStar_Syntax_Syntax.U_unif
                                          uu____13966) ->
                                           let uu____13975 =
                                             let uu____13977 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13977
                                              in
                                           failwith uu____13975
                                       | uu____13981 -> false  in
                                     let u_leq_u_k u =
                                       let uu____13994 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____13994 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14012 = u_leq_u_k u_tp  in
                                       if uu____14012
                                       then true
                                       else
                                         (let uu____14019 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14019 with
                                          | (formals,uu____14036) ->
                                              let uu____14057 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14057 with
                                               | (uu____14067,uu____14068,uu____14069,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14080 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14080
             then
               let uu____14085 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14085
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14105  ->
                       match uu___10_14105 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14109 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14122 = c  in
                 match uu____14122 with
                 | (name,args,uu____14127,uu____14128,uu____14129) ->
                     let uu____14140 =
                       let uu____14141 =
                         let uu____14153 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14180  ->
                                   match uu____14180 with
                                   | (uu____14189,sort,uu____14191) -> sort))
                            in
                         (name, uu____14153,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14141  in
                     [uu____14140]
               else
                 (let uu____14202 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14202 c)
                in
             let inversion_axioms tapp vars =
               let uu____14220 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14228 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14228 FStar_Option.isNone))
                  in
               if uu____14220
               then []
               else
                 (let uu____14263 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14263 with
                  | (xxsym,xx) ->
                      let uu____14276 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14315  ->
                                fun l  ->
                                  match uu____14315 with
                                  | (out,decls) ->
                                      let uu____14335 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14335 with
                                       | (uu____14346,data_t) ->
                                           let uu____14348 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14348 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14392 =
                                                    let uu____14393 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14393.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14392 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14396,indices)
                                                      -> indices
                                                  | uu____14422 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14452  ->
                                                            match uu____14452
                                                            with
                                                            | (x,uu____14460)
                                                                ->
                                                                let uu____14465
                                                                  =
                                                                  let uu____14466
                                                                    =
                                                                    let uu____14474
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14474,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14466
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14465)
                                                       env)
                                                   in
                                                let uu____14479 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14479 with
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
                                                                  let uu____14514
                                                                    =
                                                                    let uu____14519
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____14519,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____14514)
                                                             vars indices1
                                                         else []  in
                                                       let uu____14522 =
                                                         let uu____14523 =
                                                           let uu____14528 =
                                                             let uu____14529
                                                               =
                                                               let uu____14534
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____14535
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____14534,
                                                                 uu____14535)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____14529
                                                              in
                                                           (out, uu____14528)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____14523
                                                          in
                                                       (uu____14522,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14276 with
                       | (data_ax,decls) ->
                           let uu____14550 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____14550 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____14567 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____14567 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____14574 =
                                    let uu____14582 =
                                      let uu____14583 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____14584 =
                                        let uu____14595 =
                                          let uu____14596 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____14598 =
                                            let uu____14601 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____14601 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____14596 uu____14598
                                           in
                                        let uu____14603 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____14595,
                                          uu____14603)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____14583 uu____14584
                                       in
                                    let uu____14612 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____14582,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____14612)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____14574
                                   in
                                let uu____14618 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____14618)))
                in
             let uu____14625 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____14647 ->
                     let uu____14648 =
                       let uu____14655 =
                         let uu____14656 =
                           let uu____14671 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____14671)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____14656  in
                       FStar_Syntax_Syntax.mk uu____14655  in
                     uu____14648 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____14625 with
             | (formals,res) ->
                 let uu____14711 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____14711 with
                  | (vars,guards,env',binder_decls,uu____14736) ->
                      let arity = FStar_List.length vars  in
                      let uu____14750 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____14750 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____14776 =
                               let uu____14784 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____14784)  in
                             FStar_SMTEncoding_Util.mkApp uu____14776  in
                           let uu____14790 =
                             let tname_decl =
                               let uu____14800 =
                                 let uu____14801 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____14820 =
                                             let uu____14822 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____14822
                                              in
                                           let uu____14824 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____14820, uu____14824, false)))
                                    in
                                 let uu____14828 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____14801,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____14828, false)
                                  in
                               constructor_or_logic_type_decl uu____14800  in
                             let uu____14836 =
                               match vars with
                               | [] ->
                                   let uu____14849 =
                                     let uu____14850 =
                                       let uu____14853 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _14859  ->
                                            FStar_Pervasives_Native.Some
                                              _14859) uu____14853
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____14850
                                      in
                                   ([], uu____14849)
                               | uu____14862 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____14872 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____14872
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____14888 =
                                       let uu____14896 =
                                         let uu____14897 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14898 =
                                           let uu____14914 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____14914)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____14897 uu____14898
                                          in
                                       (uu____14896,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____14888
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____14836 with
                             | (tok_decls,env2) ->
                                 let uu____14941 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____14941
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____14790 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____14969 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____14969 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____14991 =
                                            let uu____14992 =
                                              let uu____15000 =
                                                let uu____15001 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15001
                                                 in
                                              (uu____15000,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____14992
                                             in
                                          [uu____14991]
                                        else []  in
                                      let uu____15009 =
                                        let uu____15012 =
                                          let uu____15015 =
                                            let uu____15018 =
                                              let uu____15019 =
                                                let uu____15027 =
                                                  let uu____15028 =
                                                    FStar_Ident.range_of_lid
                                                      t
                                                     in
                                                  let uu____15029 =
                                                    let uu____15040 =
                                                      FStar_SMTEncoding_Util.mkImp
                                                        (guard, k1)
                                                       in
                                                    ([[tapp]], vars,
                                                      uu____15040)
                                                     in
                                                  FStar_SMTEncoding_Term.mkForall
                                                    uu____15028 uu____15029
                                                   in
                                                (uu____15027,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15019
                                               in
                                            [uu____15018]  in
                                          FStar_List.append karr uu____15015
                                           in
                                        FStar_All.pipe_right uu____15012
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15009
                                   in
                                let aux =
                                  let uu____15059 =
                                    let uu____15062 =
                                      inversion_axioms tapp vars  in
                                    let uu____15065 =
                                      let uu____15068 =
                                        let uu____15071 =
                                          let uu____15072 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15072 env2 tapp
                                            vars
                                           in
                                        [uu____15071]  in
                                      FStar_All.pipe_right uu____15068
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15062 uu____15065
                                     in
                                  FStar_List.append kindingAx uu____15059  in
                                let g =
                                  let uu____15080 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15080
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15088,uu____15089,uu____15090,uu____15091,uu____15092)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15100,t,uu____15102,n_tps,uu____15104) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15115 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15115 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15163 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15163 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15187 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15187 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15207 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15207 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15286 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15286,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15293 =
                                   let uu____15294 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15294, true)
                                    in
                                 let uu____15302 =
                                   let uu____15309 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15309
                                    in
                                 FStar_All.pipe_right uu____15293 uu____15302
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
                               let uu____15321 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15321 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15333::uu____15334 ->
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
                                            let uu____15383 =
                                              let uu____15384 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15384]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15383
                                             in
                                          let uu____15410 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15411 =
                                            let uu____15422 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15422)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15410 uu____15411
                                      | uu____15449 -> tok_typing  in
                                    let uu____15460 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15460 with
                                     | (vars',guards',env'',decls_formals,uu____15485)
                                         ->
                                         let uu____15498 =
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
                                         (match uu____15498 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____15528 ->
                                                    let uu____15537 =
                                                      let uu____15538 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____15538
                                                       in
                                                    [uu____15537]
                                                 in
                                              let encode_elim uu____15554 =
                                                let uu____15555 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____15555 with
                                                | (head1,args) ->
                                                    let uu____15606 =
                                                      let uu____15607 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____15607.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____15606 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____15619;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____15620;_},uu____15621)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____15627 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____15627
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
                                                                  | uu____15690
                                                                    ->
                                                                    let uu____15691
                                                                    =
                                                                    let uu____15697
                                                                    =
                                                                    let uu____15699
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15699
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15697)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15691
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15722
                                                                    =
                                                                    let uu____15724
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15724
                                                                     in
                                                                    if
                                                                    uu____15722
                                                                    then
                                                                    let uu____15746
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15746]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____15749
                                                                =
                                                                let uu____15763
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____15820
                                                                     ->
                                                                    fun
                                                                    uu____15821
                                                                     ->
                                                                    match 
                                                                    (uu____15820,
                                                                    uu____15821)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15932
                                                                    =
                                                                    let uu____15940
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15940
                                                                     in
                                                                    (match uu____15932
                                                                    with
                                                                    | 
                                                                    (uu____15954,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15965
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15965
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15970
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15970
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
                                                                  uu____15763
                                                                 in
                                                              (match uu____15749
                                                               with
                                                               | (uu____15991,arg_vars,elim_eqns_or_guards,uu____15994)
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
                                                                    let uu____16021
                                                                    =
                                                                    let uu____16029
                                                                    =
                                                                    let uu____16030
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16031
                                                                    =
                                                                    let uu____16042
                                                                    =
                                                                    let uu____16043
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16043
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16045
                                                                    =
                                                                    let uu____16046
                                                                    =
                                                                    let uu____16051
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16051)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16046
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16042,
                                                                    uu____16045)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16030
                                                                    uu____16031
                                                                     in
                                                                    (uu____16029,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16021
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16066
                                                                    =
                                                                    let uu____16067
                                                                    =
                                                                    let uu____16073
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16073,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16067
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16066
                                                                     in
                                                                    let uu____16076
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16076
                                                                    then
                                                                    let x =
                                                                    let uu____16080
                                                                    =
                                                                    let uu____16086
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16086,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16080
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16091
                                                                    =
                                                                    let uu____16099
                                                                    =
                                                                    let uu____16100
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16101
                                                                    =
                                                                    let uu____16112
                                                                    =
                                                                    let uu____16117
                                                                    =
                                                                    let uu____16120
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16120]
                                                                     in
                                                                    [uu____16117]
                                                                     in
                                                                    let uu____16125
                                                                    =
                                                                    let uu____16126
                                                                    =
                                                                    let uu____16131
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16133
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16131,
                                                                    uu____16133)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16126
                                                                     in
                                                                    (uu____16112,
                                                                    [x],
                                                                    uu____16125)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16100
                                                                    uu____16101
                                                                     in
                                                                    let uu____16154
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16099,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16154)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16091
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16165
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
                                                                    (let uu____16188
                                                                    =
                                                                    let uu____16189
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16189
                                                                    dapp1  in
                                                                    [uu____16188])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16165
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16196
                                                                    =
                                                                    let uu____16204
                                                                    =
                                                                    let uu____16205
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16206
                                                                    =
                                                                    let uu____16217
                                                                    =
                                                                    let uu____16218
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16218
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16220
                                                                    =
                                                                    let uu____16221
                                                                    =
                                                                    let uu____16226
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16226)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16221
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16217,
                                                                    uu____16220)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16205
                                                                    uu____16206
                                                                     in
                                                                    (uu____16204,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16196)
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
                                                         let uu____16245 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16245
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
                                                                  | uu____16308
                                                                    ->
                                                                    let uu____16309
                                                                    =
                                                                    let uu____16315
                                                                    =
                                                                    let uu____16317
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16317
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16315)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16309
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16340
                                                                    =
                                                                    let uu____16342
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16342
                                                                     in
                                                                    if
                                                                    uu____16340
                                                                    then
                                                                    let uu____16364
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16364]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16367
                                                                =
                                                                let uu____16381
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16438
                                                                     ->
                                                                    fun
                                                                    uu____16439
                                                                     ->
                                                                    match 
                                                                    (uu____16438,
                                                                    uu____16439)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16550
                                                                    =
                                                                    let uu____16558
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16558
                                                                     in
                                                                    (match uu____16550
                                                                    with
                                                                    | 
                                                                    (uu____16572,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16583
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16583
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16588
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16588
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
                                                                  uu____16381
                                                                 in
                                                              (match uu____16367
                                                               with
                                                               | (uu____16609,arg_vars,elim_eqns_or_guards,uu____16612)
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
                                                                    let uu____16639
                                                                    =
                                                                    let uu____16647
                                                                    =
                                                                    let uu____16648
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16649
                                                                    =
                                                                    let uu____16660
                                                                    =
                                                                    let uu____16661
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16661
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16663
                                                                    =
                                                                    let uu____16664
                                                                    =
                                                                    let uu____16669
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16669)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16664
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16660,
                                                                    uu____16663)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16648
                                                                    uu____16649
                                                                     in
                                                                    (uu____16647,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16639
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16684
                                                                    =
                                                                    let uu____16685
                                                                    =
                                                                    let uu____16691
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16691,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16685
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16684
                                                                     in
                                                                    let uu____16694
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16694
                                                                    then
                                                                    let x =
                                                                    let uu____16698
                                                                    =
                                                                    let uu____16704
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16704,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16698
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16709
                                                                    =
                                                                    let uu____16717
                                                                    =
                                                                    let uu____16718
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16719
                                                                    =
                                                                    let uu____16730
                                                                    =
                                                                    let uu____16735
                                                                    =
                                                                    let uu____16738
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16738]
                                                                     in
                                                                    [uu____16735]
                                                                     in
                                                                    let uu____16743
                                                                    =
                                                                    let uu____16744
                                                                    =
                                                                    let uu____16749
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16751
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16749,
                                                                    uu____16751)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16744
                                                                     in
                                                                    (uu____16730,
                                                                    [x],
                                                                    uu____16743)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16718
                                                                    uu____16719
                                                                     in
                                                                    let uu____16772
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16717,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16772)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16709
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16783
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
                                                                    (let uu____16806
                                                                    =
                                                                    let uu____16807
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16807
                                                                    dapp1  in
                                                                    [uu____16806])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16783
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16814
                                                                    =
                                                                    let uu____16822
                                                                    =
                                                                    let uu____16823
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16824
                                                                    =
                                                                    let uu____16835
                                                                    =
                                                                    let uu____16836
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16836
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16838
                                                                    =
                                                                    let uu____16839
                                                                    =
                                                                    let uu____16844
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16844)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16839
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16835,
                                                                    uu____16838)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16823
                                                                    uu____16824
                                                                     in
                                                                    (uu____16822,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16814)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____16861 ->
                                                         ((let uu____16863 =
                                                             let uu____16869
                                                               =
                                                               let uu____16871
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____16873
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____16871
                                                                 uu____16873
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____16869)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____16863);
                                                          ([], [])))
                                                 in
                                              let uu____16881 =
                                                encode_elim ()  in
                                              (match uu____16881 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____16907 =
                                                       let uu____16910 =
                                                         let uu____16913 =
                                                           let uu____16916 =
                                                             let uu____16919
                                                               =
                                                               let uu____16922
                                                                 =
                                                                 let uu____16925
                                                                   =
                                                                   let uu____16926
                                                                    =
                                                                    let uu____16938
                                                                    =
                                                                    let uu____16939
                                                                    =
                                                                    let uu____16941
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16941
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____16939
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____16938)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____16926
                                                                    in
                                                                 [uu____16925]
                                                                  in
                                                               FStar_List.append
                                                                 uu____16922
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____16919
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____16952 =
                                                             let uu____16955
                                                               =
                                                               let uu____16958
                                                                 =
                                                                 let uu____16961
                                                                   =
                                                                   let uu____16964
                                                                    =
                                                                    let uu____16967
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____16972
                                                                    =
                                                                    let uu____16975
                                                                    =
                                                                    let uu____16976
                                                                    =
                                                                    let uu____16984
                                                                    =
                                                                    let uu____16985
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16986
                                                                    =
                                                                    let uu____16997
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16997)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16985
                                                                    uu____16986
                                                                     in
                                                                    (uu____16984,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16976
                                                                     in
                                                                    let uu____17010
                                                                    =
                                                                    let uu____17013
                                                                    =
                                                                    let uu____17014
                                                                    =
                                                                    let uu____17022
                                                                    =
                                                                    let uu____17023
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17024
                                                                    =
                                                                    let uu____17035
                                                                    =
                                                                    let uu____17036
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17036
                                                                    vars'  in
                                                                    let uu____17038
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17035,
                                                                    uu____17038)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17023
                                                                    uu____17024
                                                                     in
                                                                    (uu____17022,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17014
                                                                     in
                                                                    [uu____17013]
                                                                     in
                                                                    uu____16975
                                                                    ::
                                                                    uu____17010
                                                                     in
                                                                    uu____16967
                                                                    ::
                                                                    uu____16972
                                                                     in
                                                                   FStar_List.append
                                                                    uu____16964
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____16961
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____16958
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____16955
                                                              in
                                                           FStar_List.append
                                                             uu____16916
                                                             uu____16952
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____16913
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____16910
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____16907
                                                      in
                                                   let uu____17055 =
                                                     let uu____17056 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17056 g
                                                      in
                                                   (uu____17055, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17090  ->
              fun se  ->
                match uu____17090 with
                | (g,env1) ->
                    let uu____17110 = encode_sigelt env1 se  in
                    (match uu____17110 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17178 =
        match uu____17178 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17215 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17223 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17223
                   then
                     let uu____17228 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17230 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17232 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17228 uu____17230 uu____17232
                   else ());
                  (let uu____17237 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17237 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17255 =
                         let uu____17263 =
                           let uu____17265 =
                             let uu____17267 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17267
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17265  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17263
                          in
                       (match uu____17255 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17287 = FStar_Options.log_queries ()
                                 in
                              if uu____17287
                              then
                                let uu____17290 =
                                  let uu____17292 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17294 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17296 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17292 uu____17294 uu____17296
                                   in
                                FStar_Pervasives_Native.Some uu____17290
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17312 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17322 =
                                let uu____17325 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17325  in
                              FStar_List.append uu____17312 uu____17322  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17337,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17357 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17357 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____17378 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____17378 with | (uu____17405,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17458  ->
              match uu____17458 with
              | (l,uu____17467,uu____17468) ->
                  let uu____17471 =
                    let uu____17483 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17483, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17471))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17516  ->
              match uu____17516 with
              | (l,uu____17527,uu____17528) ->
                  let uu____17531 =
                    let uu____17532 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _17535  -> FStar_SMTEncoding_Term.Echo _17535)
                      uu____17532
                     in
                  let uu____17536 =
                    let uu____17539 =
                      let uu____17540 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17540  in
                    [uu____17539]  in
                  uu____17531 :: uu____17536))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17558 =
      let uu____17561 =
        let uu____17562 = FStar_Util.psmap_empty ()  in
        let uu____17577 =
          let uu____17586 = FStar_Util.psmap_empty ()  in (uu____17586, [])
           in
        let uu____17593 =
          let uu____17595 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____17595 FStar_Ident.string_of_lid  in
        let uu____17597 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17562;
          FStar_SMTEncoding_Env.fvar_bindings = uu____17577;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____17593;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____17597
        }  in
      [uu____17561]  in
    FStar_ST.op_Colon_Equals last_env uu____17558
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____17641 = FStar_ST.op_Bang last_env  in
      match uu____17641 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17669 ->
          let uu___1540_17672 = e  in
          let uu____17673 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1540_17672.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1540_17672.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1540_17672.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1540_17672.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1540_17672.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1540_17672.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1540_17672.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____17673;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1540_17672.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1540_17672.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____17681 = FStar_ST.op_Bang last_env  in
    match uu____17681 with
    | [] -> failwith "Empty env stack"
    | uu____17708::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____17740  ->
    let uu____17741 = FStar_ST.op_Bang last_env  in
    match uu____17741 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____17801  ->
    let uu____17802 = FStar_ST.op_Bang last_env  in
    match uu____17802 with
    | [] -> failwith "Popping an empty stack"
    | uu____17829::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____17866  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____17919  ->
         let uu____17920 = snapshot_env ()  in
         match uu____17920 with
         | (env_depth,()) ->
             let uu____17942 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____17942 with
              | (varops_depth,()) ->
                  let uu____17964 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____17964 with
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
        (fun uu____18022  ->
           let uu____18023 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18023 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18118 = snapshot msg  in () 
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
        | (uu____18164::uu____18165,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1601_18173 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1601_18173.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1601_18173.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1601_18173.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18174 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1607_18201 = elt  in
        let uu____18202 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1607_18201.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1607_18201.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18202;
          FStar_SMTEncoding_Term.a_names =
            (uu___1607_18201.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18222 =
        let uu____18225 =
          let uu____18226 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18226  in
        let uu____18227 = open_fact_db_tags env  in uu____18225 ::
          uu____18227
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18222
  
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
      let uu____18254 = encode_sigelt env se  in
      match uu____18254 with
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
                (let uu____18300 =
                   let uu____18303 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18303
                    in
                 match uu____18300 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18318 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18318
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18348 = FStar_Options.log_queries ()  in
        if uu____18348
        then
          let uu____18353 =
            let uu____18354 =
              let uu____18356 =
                let uu____18358 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18358 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18356  in
            FStar_SMTEncoding_Term.Caption uu____18354  in
          uu____18353 :: decls
        else decls  in
      (let uu____18377 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18377
       then
         let uu____18380 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18380
       else ());
      (let env =
         let uu____18386 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18386 tcenv  in
       let uu____18387 = encode_top_level_facts env se  in
       match uu____18387 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18401 =
               let uu____18404 =
                 let uu____18407 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18407
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18404  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18401)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18440 = FStar_Options.log_queries ()  in
          if uu____18440
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1645_18460 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1645_18460.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1645_18460.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1645_18460.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1645_18460.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1645_18460.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1645_18460.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1645_18460.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1645_18460.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1645_18460.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1645_18460.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18465 =
             let uu____18468 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18468
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18465  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18488 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18488
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
          (let uu____18512 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____18512
           then
             let uu____18515 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____18515
           else ());
          (let env =
             let uu____18523 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____18523
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____18562  ->
                     fun se  ->
                       match uu____18562 with
                       | (g,env2) ->
                           let uu____18582 = encode_top_level_facts env2 se
                              in
                           (match uu____18582 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____18605 =
             encode_signature
               (let uu___1668_18614 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1668_18614.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1668_18614.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1668_18614.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1668_18614.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1668_18614.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1668_18614.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1668_18614.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1668_18614.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1668_18614.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1668_18614.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____18605 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____18630 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18630
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____18636 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____18636))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____18664  ->
        match uu____18664 with
        | (decls,fvbs) ->
            ((let uu____18678 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____18678
              then ()
              else
                (let uu____18683 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18683
                 then
                   let uu____18686 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____18686
                 else ()));
             (let env =
                let uu____18694 = get_env name tcenv  in
                FStar_All.pipe_right uu____18694
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____18696 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____18696
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____18710 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____18710
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
        (let uu____18772 =
           let uu____18774 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____18774.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____18772);
        (let env =
           let uu____18776 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____18776 tcenv  in
         let uu____18777 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____18816 = aux rest  in
                 (match uu____18816 with
                  | (out,rest1) ->
                      let t =
                        let uu____18844 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____18844 with
                        | FStar_Pervasives_Native.Some uu____18847 ->
                            let uu____18848 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____18848
                              x.FStar_Syntax_Syntax.sort
                        | uu____18849 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____18853 =
                        let uu____18856 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1709_18859 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1709_18859.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1709_18859.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____18856 :: out  in
                      (uu____18853, rest1))
             | uu____18864 -> ([], bindings)  in
           let uu____18871 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____18871 with
           | (closing,bindings) ->
               let uu____18898 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____18898, bindings)
            in
         match uu____18777 with
         | (q1,bindings) ->
             let uu____18929 = encode_env_bindings env bindings  in
             (match uu____18929 with
              | (env_decls,env1) ->
                  ((let uu____18951 =
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
                    if uu____18951
                    then
                      let uu____18958 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____18958
                    else ());
                   (let uu____18963 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula
                        FStar_Pervasives_Native.None q1 env1
                       in
                    match uu____18963 with
                    | (phi,qdecls) ->
                        let uu____18985 =
                          let uu____18990 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____18990 phi
                           in
                        (match uu____18985 with
                         | (labels,phi1) ->
                             let uu____19007 = encode_labels labels  in
                             (match uu____19007 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19043 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19043
                                    then
                                      let uu____19048 =
                                        let uu____19049 =
                                          let uu____19051 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____19051
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19049
                                         in
                                      [uu____19048]
                                    else []  in
                                  let query_prelude =
                                    let uu____19059 =
                                      let uu____19060 =
                                        let uu____19061 =
                                          let uu____19064 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19071 =
                                            let uu____19074 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19074
                                             in
                                          FStar_List.append uu____19064
                                            uu____19071
                                           in
                                        FStar_List.append env_decls
                                          uu____19061
                                         in
                                      FStar_All.pipe_right uu____19060
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19059
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19084 =
                                      let uu____19092 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19093 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19092,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19093)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19084
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
  