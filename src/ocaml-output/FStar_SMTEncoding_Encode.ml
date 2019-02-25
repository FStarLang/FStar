open Prims
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
  let uu____139 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____139 with
  | (asym,a) ->
      let uu____150 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____150 with
       | (xsym,x) ->
           let uu____161 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____161 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____239 =
                      let uu____251 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____251, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____239  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____271 =
                      let uu____279 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____279)  in
                    FStar_SMTEncoding_Util.mkApp uu____271  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____298 =
                    let uu____301 =
                      let uu____304 =
                        let uu____307 =
                          let uu____308 =
                            let uu____316 =
                              let uu____317 =
                                let uu____328 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____328)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____317
                               in
                            (uu____316, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____308  in
                        let uu____340 =
                          let uu____343 =
                            let uu____344 =
                              let uu____352 =
                                let uu____353 =
                                  let uu____364 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____364)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____353
                                 in
                              (uu____352,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____344  in
                          [uu____343]  in
                        uu____307 :: uu____340  in
                      xtok_decl :: uu____304  in
                    xname_decl :: uu____301  in
                  (xtok1, (FStar_List.length vars), uu____298)  in
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
                  let uu____534 =
                    let uu____555 =
                      let uu____574 =
                        let uu____575 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____575
                         in
                      quant axy uu____574  in
                    (FStar_Parser_Const.op_Eq, uu____555)  in
                  let uu____592 =
                    let uu____615 =
                      let uu____636 =
                        let uu____655 =
                          let uu____656 =
                            let uu____657 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____657  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____656
                           in
                        quant axy uu____655  in
                      (FStar_Parser_Const.op_notEq, uu____636)  in
                    let uu____674 =
                      let uu____697 =
                        let uu____718 =
                          let uu____737 =
                            let uu____738 =
                              let uu____739 =
                                let uu____744 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____745 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____744, uu____745)  in
                              FStar_SMTEncoding_Util.mkAnd uu____739  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____738
                             in
                          quant xy uu____737  in
                        (FStar_Parser_Const.op_And, uu____718)  in
                      let uu____762 =
                        let uu____785 =
                          let uu____806 =
                            let uu____825 =
                              let uu____826 =
                                let uu____827 =
                                  let uu____832 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____833 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____832, uu____833)  in
                                FStar_SMTEncoding_Util.mkOr uu____827  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____826
                               in
                            quant xy uu____825  in
                          (FStar_Parser_Const.op_Or, uu____806)  in
                        let uu____850 =
                          let uu____873 =
                            let uu____894 =
                              let uu____913 =
                                let uu____914 =
                                  let uu____915 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____915  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____914
                                 in
                              quant qx uu____913  in
                            (FStar_Parser_Const.op_Negation, uu____894)  in
                          let uu____932 =
                            let uu____955 =
                              let uu____976 =
                                let uu____995 =
                                  let uu____996 =
                                    let uu____997 =
                                      let uu____1002 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1003 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1002, uu____1003)  in
                                    FStar_SMTEncoding_Util.mkLT uu____997  in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____996
                                   in
                                quant xy uu____995  in
                              (FStar_Parser_Const.op_LT, uu____976)  in
                            let uu____1020 =
                              let uu____1043 =
                                let uu____1064 =
                                  let uu____1083 =
                                    let uu____1084 =
                                      let uu____1085 =
                                        let uu____1090 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1091 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1090, uu____1091)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1085
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1084
                                     in
                                  quant xy uu____1083  in
                                (FStar_Parser_Const.op_LTE, uu____1064)  in
                              let uu____1108 =
                                let uu____1131 =
                                  let uu____1152 =
                                    let uu____1171 =
                                      let uu____1172 =
                                        let uu____1173 =
                                          let uu____1178 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1179 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1178, uu____1179)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1173
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1172
                                       in
                                    quant xy uu____1171  in
                                  (FStar_Parser_Const.op_GT, uu____1152)  in
                                let uu____1196 =
                                  let uu____1219 =
                                    let uu____1240 =
                                      let uu____1259 =
                                        let uu____1260 =
                                          let uu____1261 =
                                            let uu____1266 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1267 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1266, uu____1267)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1261
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1260
                                         in
                                      quant xy uu____1259  in
                                    (FStar_Parser_Const.op_GTE, uu____1240)
                                     in
                                  let uu____1284 =
                                    let uu____1307 =
                                      let uu____1328 =
                                        let uu____1347 =
                                          let uu____1348 =
                                            let uu____1349 =
                                              let uu____1354 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1355 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1354, uu____1355)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1349
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1348
                                           in
                                        quant xy uu____1347  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1328)
                                       in
                                    let uu____1372 =
                                      let uu____1395 =
                                        let uu____1416 =
                                          let uu____1435 =
                                            let uu____1436 =
                                              let uu____1437 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1437
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1436
                                             in
                                          quant qx uu____1435  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1416)
                                         in
                                      let uu____1454 =
                                        let uu____1477 =
                                          let uu____1498 =
                                            let uu____1517 =
                                              let uu____1518 =
                                                let uu____1519 =
                                                  let uu____1524 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1525 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1524, uu____1525)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1519
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1518
                                               in
                                            quant xy uu____1517  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1498)
                                           in
                                        let uu____1542 =
                                          let uu____1565 =
                                            let uu____1586 =
                                              let uu____1605 =
                                                let uu____1606 =
                                                  let uu____1607 =
                                                    let uu____1612 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____1613 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____1612, uu____1613)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____1607
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____1606
                                                 in
                                              quant xy uu____1605  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____1586)
                                             in
                                          let uu____1630 =
                                            let uu____1653 =
                                              let uu____1674 =
                                                let uu____1693 =
                                                  let uu____1694 =
                                                    let uu____1695 =
                                                      let uu____1700 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____1701 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____1700,
                                                        uu____1701)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____1695
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____1694
                                                   in
                                                quant xy uu____1693  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____1674)
                                               in
                                            let uu____1718 =
                                              let uu____1741 =
                                                let uu____1762 =
                                                  let uu____1781 =
                                                    let uu____1782 =
                                                      let uu____1783 =
                                                        let uu____1788 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____1789 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____1788,
                                                          uu____1789)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____1783
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____1782
                                                     in
                                                  quant xy uu____1781  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____1762)
                                                 in
                                              let uu____1806 =
                                                let uu____1829 =
                                                  let uu____1850 =
                                                    let uu____1869 =
                                                      let uu____1870 =
                                                        let uu____1871 =
                                                          let uu____1876 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____1877 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____1876,
                                                            uu____1877)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____1871
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____1870
                                                       in
                                                    quant xy uu____1869  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____1850)
                                                   in
                                                let uu____1894 =
                                                  let uu____1917 =
                                                    let uu____1938 =
                                                      let uu____1957 =
                                                        let uu____1958 =
                                                          let uu____1959 =
                                                            let uu____1964 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____1965 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____1964,
                                                              uu____1965)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____1959
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____1958
                                                         in
                                                      quant xy uu____1957  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____1938)
                                                     in
                                                  let uu____1982 =
                                                    let uu____2005 =
                                                      let uu____2026 =
                                                        let uu____2045 =
                                                          let uu____2046 =
                                                            let uu____2047 =
                                                              let uu____2052
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2053
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2052,
                                                                uu____2053)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2047
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2046
                                                           in
                                                        quant xy uu____2045
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2026)
                                                       in
                                                    let uu____2070 =
                                                      let uu____2093 =
                                                        let uu____2114 =
                                                          let uu____2133 =
                                                            let uu____2134 =
                                                              let uu____2135
                                                                =
                                                                let uu____2140
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2141
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2140,
                                                                  uu____2141)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2135
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2134
                                                             in
                                                          quant xy uu____2133
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2114)
                                                         in
                                                      let uu____2158 =
                                                        let uu____2181 =
                                                          let uu____2202 =
                                                            let uu____2221 =
                                                              let uu____2222
                                                                =
                                                                let uu____2223
                                                                  =
                                                                  let uu____2228
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2229
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2228,
                                                                    uu____2229)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2223
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2222
                                                               in
                                                            quant xy
                                                              uu____2221
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2202)
                                                           in
                                                        let uu____2246 =
                                                          let uu____2269 =
                                                            let uu____2290 =
                                                              let uu____2309
                                                                =
                                                                let uu____2310
                                                                  =
                                                                  let uu____2311
                                                                    =
                                                                    let uu____2316
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2317
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2316,
                                                                    uu____2317)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2311
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2310
                                                                 in
                                                              quant xy
                                                                uu____2309
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2290)
                                                             in
                                                          let uu____2334 =
                                                            let uu____2357 =
                                                              let uu____2378
                                                                =
                                                                let uu____2397
                                                                  =
                                                                  let uu____2398
                                                                    =
                                                                    let uu____2399
                                                                    =
                                                                    let uu____2404
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2405
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2404,
                                                                    uu____2405)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2399
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2398
                                                                   in
                                                                quant xy
                                                                  uu____2397
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2378)
                                                               in
                                                            let uu____2422 =
                                                              let uu____2445
                                                                =
                                                                let uu____2466
                                                                  =
                                                                  let uu____2485
                                                                    =
                                                                    let uu____2486
                                                                    =
                                                                    let uu____2487
                                                                    =
                                                                    let uu____2492
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2493
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2492,
                                                                    uu____2493)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2487
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2486
                                                                     in
                                                                  quant xy
                                                                    uu____2485
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2466)
                                                                 in
                                                              let uu____2510
                                                                =
                                                                let uu____2533
                                                                  =
                                                                  let uu____2554
                                                                    =
                                                                    let uu____2573
                                                                    =
                                                                    let uu____2574
                                                                    =
                                                                    let uu____2575
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____2575
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2574
                                                                     in
                                                                    quant qx
                                                                    uu____2573
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____2554)
                                                                   in
                                                                [uu____2533]
                                                                 in
                                                              uu____2445 ::
                                                                uu____2510
                                                               in
                                                            uu____2357 ::
                                                              uu____2422
                                                             in
                                                          uu____2269 ::
                                                            uu____2334
                                                           in
                                                        uu____2181 ::
                                                          uu____2246
                                                         in
                                                      uu____2093 ::
                                                        uu____2158
                                                       in
                                                    uu____2005 :: uu____2070
                                                     in
                                                  uu____1917 :: uu____1982
                                                   in
                                                uu____1829 :: uu____1894  in
                                              uu____1741 :: uu____1806  in
                                            uu____1653 :: uu____1718  in
                                          uu____1565 :: uu____1630  in
                                        uu____1477 :: uu____1542  in
                                      uu____1395 :: uu____1454  in
                                    uu____1307 :: uu____1372  in
                                  uu____1219 :: uu____1284  in
                                uu____1131 :: uu____1196  in
                              uu____1043 :: uu____1108  in
                            uu____955 :: uu____1020  in
                          uu____873 :: uu____932  in
                        uu____785 :: uu____850  in
                      uu____697 :: uu____762  in
                    uu____615 :: uu____674  in
                  uu____534 :: uu____592  in
                let mk1 l v1 =
                  let uu____3114 =
                    let uu____3126 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____3216  ->
                              match uu____3216 with
                              | (l',uu____3237) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3126
                      (FStar_Option.map
                         (fun uu____3336  ->
                            match uu____3336 with
                            | (uu____3364,b) ->
                                let uu____3398 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3398 v1))
                     in
                  FStar_All.pipe_right uu____3114 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____3481  ->
                          match uu____3481 with
                          | (l',uu____3502) -> FStar_Ident.lid_equals l l'))
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
          let uu____3576 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3576 with
          | (xxsym,xx) ->
              let uu____3587 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____3587 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____3603 =
                     let uu____3611 =
                       let uu____3612 =
                         let uu____3623 =
                           let uu____3624 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____3634 =
                             let uu____3645 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____3645 :: vars  in
                           uu____3624 :: uu____3634  in
                         let uu____3671 =
                           let uu____3672 =
                             let uu____3677 =
                               let uu____3678 =
                                 let uu____3683 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3683)  in
                               FStar_SMTEncoding_Util.mkEq uu____3678  in
                             (xx_has_type, uu____3677)  in
                           FStar_SMTEncoding_Util.mkImp uu____3672  in
                         ([[xx_has_type]], uu____3623, uu____3671)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____3612  in
                     let uu____3696 =
                       let uu____3698 =
                         let uu____3700 =
                           let uu____3702 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____3702  in
                         Prims.op_Hat module_name uu____3700  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3698
                        in
                     (uu____3611, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3696)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____3603)
  
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
    let uu____3758 =
      let uu____3760 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____3760  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3758  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3782 =
      let uu____3783 =
        let uu____3791 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3791, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3783  in
    let uu____3796 =
      let uu____3799 =
        let uu____3800 =
          let uu____3808 =
            let uu____3809 =
              let uu____3820 =
                let uu____3821 =
                  let uu____3826 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3826)  in
                FStar_SMTEncoding_Util.mkImp uu____3821  in
              ([[typing_pred]], [xx], uu____3820)  in
            let uu____3851 =
              let uu____3866 = FStar_TypeChecker_Env.get_range env  in
              let uu____3867 = mkForall_fuel1 env  in uu____3867 uu____3866
               in
            uu____3851 uu____3809  in
          (uu____3808, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3800  in
      [uu____3799]  in
    uu____3782 :: uu____3796  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3914 =
      let uu____3915 =
        let uu____3923 =
          let uu____3924 = FStar_TypeChecker_Env.get_range env  in
          let uu____3925 =
            let uu____3936 =
              let uu____3941 =
                let uu____3944 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3944]  in
              [uu____3941]  in
            let uu____3949 =
              let uu____3950 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3950 tt  in
            (uu____3936, [bb], uu____3949)  in
          FStar_SMTEncoding_Term.mkForall uu____3924 uu____3925  in
        (uu____3923, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3915  in
    let uu____3975 =
      let uu____3978 =
        let uu____3979 =
          let uu____3987 =
            let uu____3988 =
              let uu____3999 =
                let uu____4000 =
                  let uu____4005 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____4005)  in
                FStar_SMTEncoding_Util.mkImp uu____4000  in
              ([[typing_pred]], [xx], uu____3999)  in
            let uu____4032 =
              let uu____4047 = FStar_TypeChecker_Env.get_range env  in
              let uu____4048 = mkForall_fuel1 env  in uu____4048 uu____4047
               in
            uu____4032 uu____3988  in
          (uu____3987, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3979  in
      [uu____3978]  in
    uu____3914 :: uu____3975  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____4091 =
        let uu____4092 =
          let uu____4098 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4098, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4092  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4091  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4112 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4112  in
    let uu____4117 =
      let uu____4118 =
        let uu____4126 =
          let uu____4127 = FStar_TypeChecker_Env.get_range env  in
          let uu____4128 =
            let uu____4139 =
              let uu____4144 =
                let uu____4147 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4147]  in
              [uu____4144]  in
            let uu____4152 =
              let uu____4153 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4153 tt  in
            (uu____4139, [bb], uu____4152)  in
          FStar_SMTEncoding_Term.mkForall uu____4127 uu____4128  in
        (uu____4126, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4118  in
    let uu____4178 =
      let uu____4181 =
        let uu____4182 =
          let uu____4190 =
            let uu____4191 =
              let uu____4202 =
                let uu____4203 =
                  let uu____4208 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4208)  in
                FStar_SMTEncoding_Util.mkImp uu____4203  in
              ([[typing_pred]], [xx], uu____4202)  in
            let uu____4235 =
              let uu____4250 = FStar_TypeChecker_Env.get_range env  in
              let uu____4251 = mkForall_fuel1 env  in uu____4251 uu____4250
               in
            uu____4235 uu____4191  in
          (uu____4190, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4182  in
      let uu____4273 =
        let uu____4276 =
          let uu____4277 =
            let uu____4285 =
              let uu____4286 =
                let uu____4297 =
                  let uu____4298 =
                    let uu____4303 =
                      let uu____4304 =
                        let uu____4307 =
                          let uu____4310 =
                            let uu____4313 =
                              let uu____4314 =
                                let uu____4319 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4320 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____4319, uu____4320)  in
                              FStar_SMTEncoding_Util.mkGT uu____4314  in
                            let uu____4322 =
                              let uu____4325 =
                                let uu____4326 =
                                  let uu____4331 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4332 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____4331, uu____4332)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4326  in
                              let uu____4334 =
                                let uu____4337 =
                                  let uu____4338 =
                                    let uu____4343 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4344 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4343, uu____4344)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4338  in
                                [uu____4337]  in
                              uu____4325 :: uu____4334  in
                            uu____4313 :: uu____4322  in
                          typing_pred_y :: uu____4310  in
                        typing_pred :: uu____4307  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4304  in
                    (uu____4303, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4298  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4297)
                 in
              let uu____4377 =
                let uu____4392 = FStar_TypeChecker_Env.get_range env  in
                let uu____4393 = mkForall_fuel1 env  in uu____4393 uu____4392
                 in
              uu____4377 uu____4286  in
            (uu____4285,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4277  in
        [uu____4276]  in
      uu____4181 :: uu____4273  in
    uu____4117 :: uu____4178  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____4436 =
        let uu____4437 =
          let uu____4443 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4443, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4437  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4436  in
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
      let uu____4459 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4459  in
    let uu____4464 =
      let uu____4465 =
        let uu____4473 =
          let uu____4474 = FStar_TypeChecker_Env.get_range env  in
          let uu____4475 =
            let uu____4486 =
              let uu____4491 =
                let uu____4494 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4494]  in
              [uu____4491]  in
            let uu____4499 =
              let uu____4500 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4500 tt  in
            (uu____4486, [bb], uu____4499)  in
          FStar_SMTEncoding_Term.mkForall uu____4474 uu____4475  in
        (uu____4473, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4465  in
    let uu____4525 =
      let uu____4528 =
        let uu____4529 =
          let uu____4537 =
            let uu____4538 =
              let uu____4549 =
                let uu____4550 =
                  let uu____4555 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____4555)  in
                FStar_SMTEncoding_Util.mkImp uu____4550  in
              ([[typing_pred]], [xx], uu____4549)  in
            let uu____4582 =
              let uu____4597 = FStar_TypeChecker_Env.get_range env  in
              let uu____4598 = mkForall_fuel1 env  in uu____4598 uu____4597
               in
            uu____4582 uu____4538  in
          (uu____4537, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4529  in
      let uu____4620 =
        let uu____4623 =
          let uu____4624 =
            let uu____4632 =
              let uu____4633 =
                let uu____4644 =
                  let uu____4645 =
                    let uu____4650 =
                      let uu____4651 =
                        let uu____4654 =
                          let uu____4657 =
                            let uu____4660 =
                              let uu____4661 =
                                let uu____4666 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____4667 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____4666, uu____4667)  in
                              FStar_SMTEncoding_Util.mkGT uu____4661  in
                            let uu____4669 =
                              let uu____4672 =
                                let uu____4673 =
                                  let uu____4678 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____4679 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____4678, uu____4679)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4673  in
                              let uu____4681 =
                                let uu____4684 =
                                  let uu____4685 =
                                    let uu____4690 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____4691 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____4690, uu____4691)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4685  in
                                [uu____4684]  in
                              uu____4672 :: uu____4681  in
                            uu____4660 :: uu____4669  in
                          typing_pred_y :: uu____4657  in
                        typing_pred :: uu____4654  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4651  in
                    (uu____4650, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4645  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4644)
                 in
              let uu____4724 =
                let uu____4739 = FStar_TypeChecker_Env.get_range env  in
                let uu____4740 = mkForall_fuel1 env  in uu____4740 uu____4739
                 in
              uu____4724 uu____4633  in
            (uu____4632,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4624  in
        [uu____4623]  in
      uu____4528 :: uu____4620  in
    uu____4464 :: uu____4525  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4787 =
      let uu____4788 =
        let uu____4796 =
          let uu____4797 = FStar_TypeChecker_Env.get_range env  in
          let uu____4798 =
            let uu____4809 =
              let uu____4814 =
                let uu____4817 = FStar_SMTEncoding_Term.boxString b  in
                [uu____4817]  in
              [uu____4814]  in
            let uu____4822 =
              let uu____4823 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4823 tt  in
            (uu____4809, [bb], uu____4822)  in
          FStar_SMTEncoding_Term.mkForall uu____4797 uu____4798  in
        (uu____4796, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4788  in
    let uu____4848 =
      let uu____4851 =
        let uu____4852 =
          let uu____4860 =
            let uu____4861 =
              let uu____4872 =
                let uu____4873 =
                  let uu____4878 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____4878)  in
                FStar_SMTEncoding_Util.mkImp uu____4873  in
              ([[typing_pred]], [xx], uu____4872)  in
            let uu____4905 =
              let uu____4920 = FStar_TypeChecker_Env.get_range env  in
              let uu____4921 = mkForall_fuel1 env  in uu____4921 uu____4920
               in
            uu____4905 uu____4861  in
          (uu____4860, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4852  in
      [uu____4851]  in
    uu____4787 :: uu____4848  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____4968 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____4968]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____4998 =
      let uu____4999 =
        let uu____5007 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____5007, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4999  in
    [uu____4998]  in
  let mk_and_interp env conj uu____5030 =
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
    let uu____5059 =
      let uu____5060 =
        let uu____5068 =
          let uu____5069 = FStar_TypeChecker_Env.get_range env  in
          let uu____5070 =
            let uu____5081 =
              let uu____5082 =
                let uu____5087 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____5087, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5082  in
            ([[l_and_a_b]], [aa; bb], uu____5081)  in
          FStar_SMTEncoding_Term.mkForall uu____5069 uu____5070  in
        (uu____5068, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5060  in
    [uu____5059]  in
  let mk_or_interp env disj uu____5142 =
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
    let uu____5171 =
      let uu____5172 =
        let uu____5180 =
          let uu____5181 = FStar_TypeChecker_Env.get_range env  in
          let uu____5182 =
            let uu____5193 =
              let uu____5194 =
                let uu____5199 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5199, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5194  in
            ([[l_or_a_b]], [aa; bb], uu____5193)  in
          FStar_SMTEncoding_Term.mkForall uu____5181 uu____5182  in
        (uu____5180, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5172  in
    [uu____5171]  in
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
    let uu____5277 =
      let uu____5278 =
        let uu____5286 =
          let uu____5287 = FStar_TypeChecker_Env.get_range env  in
          let uu____5288 =
            let uu____5299 =
              let uu____5300 =
                let uu____5305 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5305, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5300  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5299)  in
          FStar_SMTEncoding_Term.mkForall uu____5287 uu____5288  in
        (uu____5286, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5278  in
    [uu____5277]  in
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
    let uu____5395 =
      let uu____5396 =
        let uu____5404 =
          let uu____5405 = FStar_TypeChecker_Env.get_range env  in
          let uu____5406 =
            let uu____5417 =
              let uu____5418 =
                let uu____5423 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5423, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5418  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5417)  in
          FStar_SMTEncoding_Term.mkForall uu____5405 uu____5406  in
        (uu____5404, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5396  in
    [uu____5395]  in
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
    let uu____5523 =
      let uu____5524 =
        let uu____5532 =
          let uu____5533 = FStar_TypeChecker_Env.get_range env  in
          let uu____5534 =
            let uu____5545 =
              let uu____5546 =
                let uu____5551 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____5551, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5546  in
            ([[l_imp_a_b]], [aa; bb], uu____5545)  in
          FStar_SMTEncoding_Term.mkForall uu____5533 uu____5534  in
        (uu____5532, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5524  in
    [uu____5523]  in
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
    let uu____5635 =
      let uu____5636 =
        let uu____5644 =
          let uu____5645 = FStar_TypeChecker_Env.get_range env  in
          let uu____5646 =
            let uu____5657 =
              let uu____5658 =
                let uu____5663 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____5663, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5658  in
            ([[l_iff_a_b]], [aa; bb], uu____5657)  in
          FStar_SMTEncoding_Term.mkForall uu____5645 uu____5646  in
        (uu____5644, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5636  in
    [uu____5635]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____5734 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____5734  in
    let uu____5739 =
      let uu____5740 =
        let uu____5748 =
          let uu____5749 = FStar_TypeChecker_Env.get_range env  in
          let uu____5750 =
            let uu____5761 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____5761)  in
          FStar_SMTEncoding_Term.mkForall uu____5749 uu____5750  in
        (uu____5748, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5740  in
    [uu____5739]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____5814 =
      let uu____5815 =
        let uu____5823 =
          let uu____5824 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____5824 range_ty  in
        let uu____5825 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____5823, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____5825)
         in
      FStar_SMTEncoding_Util.mkAssume uu____5815  in
    [uu____5814]  in
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
        let uu____5871 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____5871 x1 t  in
      let uu____5873 = FStar_TypeChecker_Env.get_range env  in
      let uu____5874 =
        let uu____5885 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____5885)  in
      FStar_SMTEncoding_Term.mkForall uu____5873 uu____5874  in
    let uu____5910 =
      let uu____5911 =
        let uu____5919 =
          let uu____5920 = FStar_TypeChecker_Env.get_range env  in
          let uu____5921 =
            let uu____5932 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____5932)  in
          FStar_SMTEncoding_Term.mkForall uu____5920 uu____5921  in
        (uu____5919,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5911  in
    [uu____5910]  in
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
    let uu____5993 =
      let uu____5994 =
        let uu____6002 =
          let uu____6003 = FStar_TypeChecker_Env.get_range env  in
          let uu____6004 =
            let uu____6020 =
              let uu____6021 =
                let uu____6026 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____6027 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____6026, uu____6027)  in
              FStar_SMTEncoding_Util.mkAnd uu____6021  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____6020)
             in
          FStar_SMTEncoding_Term.mkForall' uu____6003 uu____6004  in
        (uu____6002,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5994  in
    [uu____5993]  in
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
          let uu____6585 =
            FStar_Util.find_opt
              (fun uu____6623  ->
                 match uu____6623 with
                 | (l,uu____6639) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____6585 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____6682,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____6743 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____6743 with
        | (form,decls) ->
            let uu____6752 =
              let uu____6755 =
                let uu____6758 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____6758]  in
              FStar_All.pipe_right uu____6755
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____6752
  
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
              let uu____6817 =
                ((let uu____6821 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____6821) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____6817
              then
                let arg_sorts =
                  let uu____6833 =
                    let uu____6834 = FStar_Syntax_Subst.compress t_norm  in
                    uu____6834.FStar_Syntax_Syntax.n  in
                  match uu____6833 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6840) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6878  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6885 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6887 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6887 with
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
                    let uu____6923 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____6923, env1)
              else
                (let uu____6928 = prims.is lid  in
                 if uu____6928
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6937 = prims.mk lid vname  in
                   match uu____6937 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____6961 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____6961, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6970 =
                      let uu____6989 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____6989 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7017 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7017
                            then
                              let uu____7022 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___23_7025 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___23_7025.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___23_7025.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___23_7025.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___23_7025.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___23_7025.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___23_7025.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___23_7025.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___23_7025.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___23_7025.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___23_7025.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___23_7025.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___23_7025.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___23_7025.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___23_7025.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___23_7025.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___23_7025.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___23_7025.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___23_7025.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___23_7025.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___23_7025.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___23_7025.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___23_7025.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___23_7025.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___23_7025.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___23_7025.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___23_7025.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___23_7025.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___23_7025.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___23_7025.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___23_7025.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___23_7025.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___23_7025.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___23_7025.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___23_7025.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___23_7025.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___23_7025.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___23_7025.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___23_7025.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___23_7025.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___23_7025.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___23_7025.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___23_7025.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7022
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7048 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____7048)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6970 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___12_7154  ->
                                  match uu___12_7154 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7158 = FStar_Util.prefix vars
                                         in
                                      (match uu____7158 with
                                       | (uu____7191,xxv) ->
                                           let xx =
                                             let uu____7230 =
                                               let uu____7231 =
                                                 let uu____7237 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7237,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7231
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7230
                                              in
                                           let uu____7240 =
                                             let uu____7241 =
                                               let uu____7249 =
                                                 let uu____7250 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7251 =
                                                   let uu____7262 =
                                                     let uu____7263 =
                                                       let uu____7268 =
                                                         let uu____7269 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7269
                                                          in
                                                       (vapp, uu____7268)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7263
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7262)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7250 uu____7251
                                                  in
                                               (uu____7249,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7241
                                              in
                                           [uu____7240])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7284 = FStar_Util.prefix vars
                                         in
                                      (match uu____7284 with
                                       | (uu____7317,xxv) ->
                                           let xx =
                                             let uu____7356 =
                                               let uu____7357 =
                                                 let uu____7363 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7363,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7357
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7356
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
                                           let uu____7374 =
                                             let uu____7375 =
                                               let uu____7383 =
                                                 let uu____7384 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7385 =
                                                   let uu____7396 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7396)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7384 uu____7385
                                                  in
                                               (uu____7383,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7375
                                              in
                                           [uu____7374])
                                  | uu____7409 -> []))
                           in
                        let uu____7410 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7410 with
                         | (vars,guards,env',decls1,uu____7435) ->
                             let uu____7448 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7461 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7461, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7465 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7465 with
                                    | (g,ds) ->
                                        let uu____7478 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7478,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7448 with
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
                                  let should_thunk uu____7501 =
                                    let is_type1 t =
                                      let uu____7509 =
                                        let uu____7510 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7510.FStar_Syntax_Syntax.n  in
                                      match uu____7509 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7514 -> true
                                      | uu____7516 -> false  in
                                    let is_squash1 t =
                                      let uu____7525 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____7525 with
                                      | (head1,uu____7544) ->
                                          let uu____7569 =
                                            let uu____7570 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____7570.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7569 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____7575;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____7576;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____7578;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____7579;_};_},uu____7580)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____7588 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____7593 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____7593))
                                       &&
                                       (let uu____7599 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____7599))
                                      &&
                                      (let uu____7602 = is_type1 t_norm  in
                                       Prims.op_Negation uu____7602)
                                     in
                                  let uu____7604 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____7663 -> (false, vars)  in
                                  (match uu____7604 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____7713 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____7713 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____7749 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____7758 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____7758
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____7769 ->
                                                  let uu____7778 =
                                                    let uu____7786 =
                                                      get_vtok ()  in
                                                    (uu____7786, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7778
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____7793 =
                                                let uu____7801 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____7801)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____7793
                                               in
                                            let uu____7815 =
                                              let vname_decl =
                                                let uu____7823 =
                                                  let uu____7835 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____7835,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____7823
                                                 in
                                              let uu____7846 =
                                                let env2 =
                                                  let uu___24_7852 = env1  in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___24_7852.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____7853 =
                                                  let uu____7855 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____7855
                                                   in
                                                if uu____7853
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____7846 with
                                              | (tok_typing,decls2) ->
                                                  let uu____7872 =
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
                                                        let uu____7898 =
                                                          let uu____7901 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____7901
                                                           in
                                                        let uu____7908 =
                                                          let uu____7909 =
                                                            let uu____7912 =
                                                              let uu____7913
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____7913
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _0_1  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _0_1)
                                                              uu____7912
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____7909
                                                           in
                                                        (uu____7898,
                                                          uu____7908)
                                                    | uu____7923 when thunked
                                                        ->
                                                        let uu____7934 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____7934
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____7949
                                                                 =
                                                                 let uu____7957
                                                                   =
                                                                   let uu____7960
                                                                    =
                                                                    let uu____7963
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____7963]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____7960
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____7957)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____7949
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____7971 =
                                                               let uu____7979
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____7979,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7971
                                                              in
                                                           let uu____7984 =
                                                             let uu____7987 =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____7987
                                                              in
                                                           (uu____7984, env1))
                                                    | uu____7996 ->
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
                                                          let uu____8020 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____8021 =
                                                            let uu____8032 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____8032)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____8020
                                                            uu____8021
                                                           in
                                                        let name_tok_corr =
                                                          let uu____8042 =
                                                            let uu____8050 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____8050,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8042
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
                                                            let uu____8061 =
                                                              let uu____8062
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8062]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8061
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8089 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8090 =
                                                              let uu____8101
                                                                =
                                                                let uu____8102
                                                                  =
                                                                  let uu____8107
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8108
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8107,
                                                                    uu____8108)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8102
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8101)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8089
                                                              uu____8090
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8137 =
                                                          let uu____8140 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8140
                                                           in
                                                        (uu____8137, env1)
                                                     in
                                                  (match uu____7872 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8161 =
                                                         let uu____8164 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8164
                                                           tok_decl
                                                          in
                                                       (uu____8161, env2))
                                               in
                                            (match uu____7815 with
                                             | (decls2,env2) ->
                                                 let uu____8183 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8193 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8193 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8208 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8208, decls)
                                                    in
                                                 (match uu____8183 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8223 =
                                                          let uu____8231 =
                                                            let uu____8232 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8233 =
                                                              let uu____8244
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8244)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8232
                                                              uu____8233
                                                             in
                                                          (uu____8231,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8223
                                                         in
                                                      let freshness =
                                                        let uu____8260 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8260
                                                        then
                                                          let uu____8268 =
                                                            let uu____8269 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8270 =
                                                              let uu____8283
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8290
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8283,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8290)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8269
                                                              uu____8270
                                                             in
                                                          let uu____8296 =
                                                            let uu____8299 =
                                                              let uu____8300
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8300
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8299]  in
                                                          uu____8268 ::
                                                            uu____8296
                                                        else []  in
                                                      let g =
                                                        let uu____8306 =
                                                          let uu____8309 =
                                                            let uu____8312 =
                                                              let uu____8315
                                                                =
                                                                let uu____8318
                                                                  =
                                                                  let uu____8321
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8321
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8318
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8315
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8312
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8309
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8306
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
          let uu____8361 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8361 with
          | FStar_Pervasives_Native.None  ->
              let uu____8372 = encode_free_var false env x t t_norm []  in
              (match uu____8372 with
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
            let tt = FStar_SMTEncoding_EncodeTerm.norm env t  in
            let uu____8435 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8435 with
            | (decls,env1) ->
                let uu____8446 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8446
                then
                  let uu____8453 =
                    let uu____8454 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8454  in
                  (uu____8453, env1)
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
             (fun uu____8510  ->
                fun lb  ->
                  match uu____8510 with
                  | (decls,env1) ->
                      let uu____8530 =
                        let uu____8535 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8535
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8530 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8564 = FStar_Syntax_Util.head_and_args t  in
    match uu____8564 with
    | (hd1,args) ->
        let uu____8608 =
          let uu____8609 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8609.FStar_Syntax_Syntax.n  in
        (match uu____8608 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8615,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____8639 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____8650 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___25_8658 = en  in
    let uu____8659 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___25_8658.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___25_8658.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___25_8658.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___25_8658.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___25_8658.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___25_8658.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___25_8658.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___25_8658.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___25_8658.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___25_8658.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____8659
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____8689  ->
      fun quals  ->
        match uu____8689 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8794 = FStar_Util.first_N nbinders formals  in
              match uu____8794 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____8895  ->
                         fun uu____8896  ->
                           match (uu____8895, uu____8896) with
                           | ((formal,uu____8922),(binder,uu____8924)) ->
                               let uu____8945 =
                                 let uu____8952 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____8952)  in
                               FStar_Syntax_Syntax.NT uu____8945) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____8966 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____9007  ->
                              match uu____9007 with
                              | (x,i) ->
                                  let uu____9026 =
                                    let uu___26_9027 = x  in
                                    let uu____9028 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___26_9027.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___26_9027.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9028
                                    }  in
                                  (uu____9026, i)))
                       in
                    FStar_All.pipe_right uu____8966
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9052 =
                      let uu____9057 = FStar_Syntax_Subst.compress body  in
                      let uu____9058 =
                        let uu____9059 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9059
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____9057 uu____9058
                       in
                    uu____9052 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___27_9110 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___27_9110.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___27_9110.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___27_9110.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___27_9110.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___27_9110.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___27_9110.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___27_9110.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___27_9110.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___27_9110.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___27_9110.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___27_9110.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___27_9110.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___27_9110.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___27_9110.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___27_9110.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___27_9110.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___27_9110.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___27_9110.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___27_9110.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___27_9110.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___27_9110.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___27_9110.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___27_9110.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___27_9110.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___27_9110.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___27_9110.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___27_9110.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___27_9110.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___27_9110.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___27_9110.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___27_9110.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___27_9110.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___27_9110.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___27_9110.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___27_9110.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___27_9110.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___27_9110.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___27_9110.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___27_9110.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___27_9110.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___27_9110.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___27_9110.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____9182  ->
                       fun uu____9183  ->
                         match (uu____9182, uu____9183) with
                         | ((x,uu____9209),(b,uu____9211)) ->
                             let uu____9232 =
                               let uu____9239 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9239)  in
                             FStar_Syntax_Syntax.NT uu____9232) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9264 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9264
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9293 ->
                    let uu____9300 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9300
                | uu____9301 when Prims.op_Negation norm1 ->
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
                | uu____9304 ->
                    let uu____9305 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9305)
                 in
              let aux t1 e1 =
                let uu____9347 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9347 with
                | (binders,body,lopt) ->
                    let uu____9379 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9395 -> arrow_formals_comp_norm false t1  in
                    (match uu____9379 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9429 =
                           if nformals < nbinders
                           then
                             let uu____9473 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9473 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9557 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9557)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9597 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9597 with
                                | (binders1,body1) ->
                                    let uu____9650 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____9650))
                             else
                               (let uu____9663 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____9663))
                            in
                         (match uu____9429 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____9723 = aux t e  in
              match uu____9723 with
              | (binders,body,comp) ->
                  let uu____9769 =
                    let uu____9780 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____9780
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____9795 = aux comp1 body1  in
                      match uu____9795 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____9769 with
                   | (binders1,body1,comp1) ->
                       let uu____9878 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____9878, comp1))
               in
            (try
               (fun uu___29_9905  ->
                  match () with
                  | () ->
                      let uu____9912 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9912
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9928 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9991  ->
                                   fun lb  ->
                                     match uu____9991 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____10046 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____10046
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____10052 =
                                             let uu____10061 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____10061
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____10052 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9928 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10202;
                                    FStar_Syntax_Syntax.lbeff = uu____10203;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10205;
                                    FStar_Syntax_Syntax.lbpos = uu____10206;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10230 =
                                     let uu____10237 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10237 with
                                     | (tcenv',uu____10253,e_t) ->
                                         let uu____10259 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10270 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10259 with
                                          | (e1,t_norm1) ->
                                              ((let uu___30_10287 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___30_10287.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10230 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10297 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10297 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10317 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10317
                                               then
                                                 let uu____10322 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10325 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10322 uu____10325
                                               else ());
                                              (let uu____10330 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10330 with
                                               | (vars,_guards,env'1,binder_decls,uu____10357)
                                                   ->
                                                   let uu____10370 =
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
                                                         let uu____10387 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10387
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10409 =
                                                          let uu____10410 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10411 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10410 fvb
                                                            uu____10411
                                                           in
                                                        (vars, uu____10409))
                                                      in
                                                   (match uu____10370 with
                                                    | (vars1,app) ->
                                                        let uu____10422 =
                                                          let is_logical =
                                                            let uu____10435 =
                                                              let uu____10436
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10436.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10435
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10442 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10446 =
                                                              let uu____10447
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10447
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10446
                                                              (fun lid  ->
                                                                 let uu____10456
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10456
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10457 =
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
                                                          if uu____10457
                                                          then
                                                            let uu____10473 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10474 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10473,
                                                              uu____10474)
                                                          else
                                                            (let uu____10485
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10485))
                                                           in
                                                        (match uu____10422
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10509
                                                                 =
                                                                 let uu____10517
                                                                   =
                                                                   let uu____10518
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10519
                                                                    =
                                                                    let uu____10530
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10530)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10518
                                                                    uu____10519
                                                                    in
                                                                 let uu____10539
                                                                   =
                                                                   let uu____10540
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10540
                                                                    in
                                                                 (uu____10517,
                                                                   uu____10539,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10509
                                                                in
                                                             let uu____10546
                                                               =
                                                               let uu____10549
                                                                 =
                                                                 let uu____10552
                                                                   =
                                                                   let uu____10555
                                                                    =
                                                                    let uu____10558
                                                                    =
                                                                    let uu____10561
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10561
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10558
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10555
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10552
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10549
                                                                in
                                                             (uu____10546,
                                                               env2)))))))
                               | uu____10570 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10630 =
                                   let uu____10636 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____10636,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10630  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10642 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10695  ->
                                         fun fvb  ->
                                           match uu____10695 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10750 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10750
                                                  in
                                               let gtok =
                                                 let uu____10754 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10754
                                                  in
                                               let env4 =
                                                 let uu____10757 =
                                                   let uu____10760 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____10760
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10757
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10642 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10885
                                     t_norm uu____10887 =
                                     match (uu____10885, uu____10887) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10917;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10918;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10920;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10921;_})
                                         ->
                                         let uu____10948 =
                                           let uu____10955 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10955 with
                                           | (tcenv',uu____10971,e_t) ->
                                               let uu____10977 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10988 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10977 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___31_11005 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___31_11005.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10948 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____11018 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____11018
                                                then
                                                  let uu____11023 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____11025 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____11027 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____11023 uu____11025
                                                    uu____11027
                                                else ());
                                               (let uu____11032 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____11032 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____11059 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____11059 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11081 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11081
                                                           then
                                                             let uu____11086
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11088
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11091
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11093
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11086
                                                               uu____11088
                                                               uu____11091
                                                               uu____11093
                                                           else ());
                                                          (let uu____11098 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11098
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11127)
                                                               ->
                                                               let uu____11140
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11153
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11153,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11157
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11157
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11170
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11170,
                                                                    decls0))
                                                                  in
                                                               (match uu____11140
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
                                                                    let uu____11191
                                                                    =
                                                                    let uu____11203
                                                                    =
                                                                    let uu____11206
                                                                    =
                                                                    let uu____11209
                                                                    =
                                                                    let uu____11212
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11212
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11209
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11206
                                                                     in
                                                                    (g,
                                                                    uu____11203,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11191
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
                                                                    let uu____11242
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11242
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
                                                                    let uu____11257
                                                                    =
                                                                    let uu____11260
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11260
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11257
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11266
                                                                    =
                                                                    let uu____11269
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11269
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11266
                                                                     in
                                                                    let uu____11274
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11274
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11290
                                                                    =
                                                                    let uu____11298
                                                                    =
                                                                    let uu____11299
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11300
                                                                    =
                                                                    let uu____11316
                                                                    =
                                                                    let uu____11317
                                                                    =
                                                                    let uu____11322
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11322)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11317
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11316)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11299
                                                                    uu____11300
                                                                     in
                                                                    let uu____11336
                                                                    =
                                                                    let uu____11337
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11337
                                                                     in
                                                                    (uu____11298,
                                                                    uu____11336,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11290
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11344
                                                                    =
                                                                    let uu____11352
                                                                    =
                                                                    let uu____11353
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11354
                                                                    =
                                                                    let uu____11365
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11365)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11353
                                                                    uu____11354
                                                                     in
                                                                    (uu____11352,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11344
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11379
                                                                    =
                                                                    let uu____11387
                                                                    =
                                                                    let uu____11388
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11389
                                                                    =
                                                                    let uu____11400
                                                                    =
                                                                    let uu____11401
                                                                    =
                                                                    let uu____11406
                                                                    =
                                                                    let uu____11407
                                                                    =
                                                                    let uu____11410
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11410
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11407
                                                                     in
                                                                    (gsapp,
                                                                    uu____11406)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11401
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11400)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11388
                                                                    uu____11389
                                                                     in
                                                                    (uu____11387,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11379
                                                                     in
                                                                    let uu____11424
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
                                                                    let uu____11436
                                                                    =
                                                                    let uu____11437
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11437
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11436
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____11439
                                                                    =
                                                                    let uu____11447
                                                                    =
                                                                    let uu____11448
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11449
                                                                    =
                                                                    let uu____11460
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11460)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11448
                                                                    uu____11449
                                                                     in
                                                                    (uu____11447,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11439
                                                                     in
                                                                    let uu____11473
                                                                    =
                                                                    let uu____11482
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11482
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11497
                                                                    =
                                                                    let uu____11500
                                                                    =
                                                                    let uu____11501
                                                                    =
                                                                    let uu____11509
                                                                    =
                                                                    let uu____11510
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11511
                                                                    =
                                                                    let uu____11522
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11522)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11510
                                                                    uu____11511
                                                                     in
                                                                    (uu____11509,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11501
                                                                     in
                                                                    [uu____11500]
                                                                     in
                                                                    (d3,
                                                                    uu____11497)
                                                                     in
                                                                    match uu____11473
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11424
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11579
                                                                    =
                                                                    let uu____11582
                                                                    =
                                                                    let uu____11585
                                                                    =
                                                                    let uu____11588
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11588
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11585
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11582
                                                                     in
                                                                    let uu____11595
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11579,
                                                                    uu____11595,
                                                                    env02))))))))))
                                      in
                                   let uu____11600 =
                                     let uu____11613 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11676  ->
                                          fun uu____11677  ->
                                            match (uu____11676, uu____11677)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11802 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11802 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11613
                                      in
                                   (match uu____11600 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11869 =
                                          let isDeclFun uu___13_11886 =
                                            match uu___13_11886 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11888 -> true
                                            | uu____11901 -> false  in
                                          let uu____11903 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11903
                                            (fun decls3  ->
                                               let uu____11933 =
                                                 FStar_List.fold_left
                                                   (fun uu____11964  ->
                                                      fun elt  ->
                                                        match uu____11964
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____12005 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____12005
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____12033
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____12033
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
                                                                    let uu___32_12071
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___32_12071.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___32_12071.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___32_12071.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____11933 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12103 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12103, elts, rest))
                                           in
                                        (match uu____11869 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12132 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___14_12138  ->
                                        match uu___14_12138 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12141 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12149 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12149)))
                                in
                             if uu____12132
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___34_12171  ->
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
                   let uu____12210 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12210
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12229 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12229, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12285 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12285 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12291 = encode_sigelt' env se  in
      match uu____12291 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12303 =
                  let uu____12306 =
                    let uu____12307 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12307  in
                  [uu____12306]  in
                FStar_All.pipe_right uu____12303
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12312 ->
                let uu____12313 =
                  let uu____12316 =
                    let uu____12319 =
                      let uu____12320 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12320  in
                    [uu____12319]  in
                  FStar_All.pipe_right uu____12316
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12327 =
                  let uu____12330 =
                    let uu____12333 =
                      let uu____12336 =
                        let uu____12337 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12337  in
                      [uu____12336]  in
                    FStar_All.pipe_right uu____12333
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12330  in
                FStar_List.append uu____12313 uu____12327
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12351 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12351
       then
         let uu____12356 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12356
       else ());
      (let is_opaque_to_smt t =
         let uu____12368 =
           let uu____12369 = FStar_Syntax_Subst.compress t  in
           uu____12369.FStar_Syntax_Syntax.n  in
         match uu____12368 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12374)) -> s = "opaque_to_smt"
         | uu____12379 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12388 =
           let uu____12389 = FStar_Syntax_Subst.compress t  in
           uu____12389.FStar_Syntax_Syntax.n  in
         match uu____12388 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12394)) -> s = "uninterpreted_by_smt"
         | uu____12399 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12405 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12411 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12423 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12424 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12425 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12438 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12440 =
             let uu____12442 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12442  in
           if uu____12440
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12471 ->
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
                let uu____12503 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12503 with
                | (formals,uu____12523) ->
                    let arity = FStar_List.length formals  in
                    let uu____12547 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12547 with
                     | (aname,atok,env2) ->
                         let uu____12573 =
                           let uu____12578 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____12578 env2
                            in
                         (match uu____12573 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12590 =
                                  let uu____12591 =
                                    let uu____12603 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____12623  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12603,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12591
                                   in
                                [uu____12590;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____12640 =
                                let aux uu____12686 uu____12687 =
                                  match (uu____12686, uu____12687) with
                                  | ((bv,uu____12731),(env3,acc_sorts,acc))
                                      ->
                                      let uu____12763 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____12763 with
                                       | (xxsym,xx,env4) ->
                                           let uu____12786 =
                                             let uu____12789 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____12789 :: acc_sorts  in
                                           (env4, uu____12786, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____12640 with
                               | (uu____12821,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____12837 =
                                       let uu____12845 =
                                         let uu____12846 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12847 =
                                           let uu____12858 =
                                             let uu____12859 =
                                               let uu____12864 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____12864)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____12859
                                              in
                                           ([[app]], xs_sorts, uu____12858)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12846 uu____12847
                                          in
                                       (uu____12845,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12837
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____12879 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____12879
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____12882 =
                                       let uu____12890 =
                                         let uu____12891 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12892 =
                                           let uu____12903 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____12903)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12891 uu____12892
                                          in
                                       (uu____12890,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12882
                                      in
                                   let uu____12916 =
                                     let uu____12919 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____12919  in
                                   (env2, uu____12916))))
                 in
              let uu____12928 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____12928 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12954,uu____12955)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____12956 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____12956 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12978,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____12985 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___15_12991  ->
                       match uu___15_12991 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____12994 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____13000 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____13003 -> false))
                in
             Prims.op_Negation uu____12985  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____13013 =
                let uu____13018 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____13018 env fv t quals  in
              match uu____13013 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____13032 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____13032  in
                  let uu____13035 =
                    let uu____13036 =
                      let uu____13039 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____13039
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____13036  in
                  (uu____13035, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13049 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13049 with
            | (uvs,f1) ->
                let env1 =
                  let uu___35_13061 = env  in
                  let uu____13062 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___35_13061.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___35_13061.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___35_13061.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13062;
                    FStar_SMTEncoding_Env.warn =
                      (uu___35_13061.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___35_13061.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___35_13061.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___35_13061.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___35_13061.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___35_13061.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___35_13061.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____13064 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13064 with
                 | (f3,decls) ->
                     let g =
                       let uu____13078 =
                         let uu____13081 =
                           let uu____13082 =
                             let uu____13090 =
                               let uu____13091 =
                                 let uu____13093 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13093
                                  in
                               FStar_Pervasives_Native.Some uu____13091  in
                             let uu____13097 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13090, uu____13097)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13082  in
                         [uu____13081]  in
                       FStar_All.pipe_right uu____13078
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13106) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13120 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13142 =
                        let uu____13145 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13145.FStar_Syntax_Syntax.fv_name  in
                      uu____13142.FStar_Syntax_Syntax.v  in
                    let uu____13146 =
                      let uu____13148 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13148  in
                    if uu____13146
                    then
                      let val_decl =
                        let uu___36_13180 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___36_13180.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___36_13180.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___36_13180.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____13181 = encode_sigelt' env1 val_decl  in
                      match uu____13181 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13120 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13217,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13219;
                           FStar_Syntax_Syntax.lbtyp = uu____13220;
                           FStar_Syntax_Syntax.lbeff = uu____13221;
                           FStar_Syntax_Syntax.lbdef = uu____13222;
                           FStar_Syntax_Syntax.lbattrs = uu____13223;
                           FStar_Syntax_Syntax.lbpos = uu____13224;_}::[]),uu____13225)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13244 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____13244 with
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
                  let uu____13282 =
                    let uu____13285 =
                      let uu____13286 =
                        let uu____13294 =
                          let uu____13295 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13296 =
                            let uu____13307 =
                              let uu____13308 =
                                let uu____13313 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13313)  in
                              FStar_SMTEncoding_Util.mkEq uu____13308  in
                            ([[b2t_x]], [xx], uu____13307)  in
                          FStar_SMTEncoding_Term.mkForall uu____13295
                            uu____13296
                           in
                        (uu____13294,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13286  in
                    [uu____13285]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13282
                   in
                let uu____13351 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13351, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13354,uu____13355) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___16_13365  ->
                   match uu___16_13365 with
                   | FStar_Syntax_Syntax.Discriminator uu____13367 -> true
                   | uu____13369 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13371,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13383 =
                      let uu____13385 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13385.FStar_Ident.idText  in
                    uu____13383 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___17_13392  ->
                      match uu___17_13392 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13395 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13398) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___18_13412  ->
                   match uu___18_13412 with
                   | FStar_Syntax_Syntax.Projector uu____13414 -> true
                   | uu____13420 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13424 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13424 with
            | FStar_Pervasives_Native.Some uu____13431 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___37_13433 = se  in
                  let uu____13434 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13434;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___37_13433.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___37_13433.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___37_13433.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13437) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13452) ->
           let uu____13461 = encode_sigelts env ses  in
           (match uu____13461 with
            | (g,env1) ->
                let uu____13472 =
                  FStar_List.fold_left
                    (fun uu____13496  ->
                       fun elt  ->
                         match uu____13496 with
                         | (g',inversions) ->
                             let uu____13524 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___19_13547  ->
                                       match uu___19_13547 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13549;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13550;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13551;_}
                                           -> false
                                       | uu____13558 -> true))
                                in
                             (match uu____13524 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___38_13583 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___38_13583.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___38_13583.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___38_13583.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13472 with
                 | (g',inversions) ->
                     let uu____13602 =
                       FStar_List.fold_left
                         (fun uu____13633  ->
                            fun elt  ->
                              match uu____13633 with
                              | (decls,elts,rest) ->
                                  let uu____13674 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___20_13683  ->
                                            match uu___20_13683 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____13685 -> true
                                            | uu____13698 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____13674
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____13721 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___21_13742  ->
                                               match uu___21_13742 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____13744 -> true
                                               | uu____13757 -> false))
                                        in
                                     match uu____13721 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___39_13788 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___39_13788.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___39_13788.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___39_13788.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____13602 with
                      | (decls,elts,rest) ->
                          let uu____13814 =
                            let uu____13815 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____13822 =
                              let uu____13825 =
                                let uu____13828 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____13828  in
                              FStar_List.append elts uu____13825  in
                            FStar_List.append uu____13815 uu____13822  in
                          (uu____13814, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____13839,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____13852 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____13852 with
             | (usubst,uvs) ->
                 let uu____13872 =
                   let uu____13879 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____13880 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____13881 =
                     let uu____13882 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____13882 k  in
                   (uu____13879, uu____13880, uu____13881)  in
                 (match uu____13872 with
                  | (env1,tps1,k1) ->
                      let uu____13895 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____13895 with
                       | (tps2,k2) ->
                           let uu____13903 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____13903 with
                            | (uu____13919,k3) ->
                                let uu____13941 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____13941 with
                                 | (tps3,env_tps,uu____13953,us) ->
                                     let u_k =
                                       let uu____13956 =
                                         let uu____13957 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____13958 =
                                           let uu____13963 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____13965 =
                                             let uu____13966 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____13966
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____13963 uu____13965
                                            in
                                         uu____13958
                                           FStar_Pervasives_Native.None
                                           uu____13957
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____13956 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____13986) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____13992,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____13995) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____14003,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____14010) ->
                                           let uu____14011 =
                                             let uu____14013 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14013
                                              in
                                           failwith uu____14011
                                       | (uu____14017,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____14018 =
                                             let uu____14020 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14020
                                              in
                                           failwith uu____14018
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14024,uu____14025) ->
                                           let uu____14034 =
                                             let uu____14036 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14036
                                              in
                                           failwith uu____14034
                                       | (uu____14040,FStar_Syntax_Syntax.U_unif
                                          uu____14041) ->
                                           let uu____14050 =
                                             let uu____14052 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14052
                                              in
                                           failwith uu____14050
                                       | uu____14056 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14069 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14069 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14087 = u_leq_u_k u_tp  in
                                       if uu____14087
                                       then true
                                       else
                                         (let uu____14094 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14094 with
                                          | (formals,uu____14111) ->
                                              let uu____14132 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14132 with
                                               | (uu____14142,uu____14143,uu____14144,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14155 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14155
             then
               let uu____14160 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14160
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___22_14180  ->
                       match uu___22_14180 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14184 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14197 = c  in
                 match uu____14197 with
                 | (name,args,uu____14202,uu____14203,uu____14204) ->
                     let uu____14215 =
                       let uu____14216 =
                         let uu____14228 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14255  ->
                                   match uu____14255 with
                                   | (uu____14264,sort,uu____14266) -> sort))
                            in
                         (name, uu____14228,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14216  in
                     [uu____14215]
               else
                 (let uu____14277 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14277 c)
                in
             let inversion_axioms tapp vars =
               let uu____14295 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14303 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14303 FStar_Option.isNone))
                  in
               if uu____14295
               then []
               else
                 (let uu____14338 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14338 with
                  | (xxsym,xx) ->
                      let uu____14351 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14390  ->
                                fun l  ->
                                  match uu____14390 with
                                  | (out,decls) ->
                                      let uu____14410 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14410 with
                                       | (uu____14421,data_t) ->
                                           let uu____14423 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14423 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14467 =
                                                    let uu____14468 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14468.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14467 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14471,indices)
                                                      -> indices
                                                  | uu____14497 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14527  ->
                                                            match uu____14527
                                                            with
                                                            | (x,uu____14535)
                                                                ->
                                                                let uu____14540
                                                                  =
                                                                  let uu____14541
                                                                    =
                                                                    let uu____14549
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14549,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14541
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14540)
                                                       env)
                                                   in
                                                let uu____14554 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14554 with
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
                                                                  let uu____14589
                                                                    =
                                                                    let uu____14594
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____14594,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____14589)
                                                             vars indices1
                                                         else []  in
                                                       let uu____14597 =
                                                         let uu____14598 =
                                                           let uu____14603 =
                                                             let uu____14604
                                                               =
                                                               let uu____14609
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____14610
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____14609,
                                                                 uu____14610)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____14604
                                                              in
                                                           (out, uu____14603)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____14598
                                                          in
                                                       (uu____14597,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14351 with
                       | (data_ax,decls) ->
                           let uu____14625 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____14625 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____14642 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____14642 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____14649 =
                                    let uu____14657 =
                                      let uu____14658 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____14659 =
                                        let uu____14670 =
                                          let uu____14671 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____14673 =
                                            let uu____14676 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____14676 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____14671 uu____14673
                                           in
                                        let uu____14678 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____14670,
                                          uu____14678)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____14658 uu____14659
                                       in
                                    let uu____14687 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____14657,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____14687)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____14649
                                   in
                                let uu____14693 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____14693)))
                in
             let uu____14700 =
               let uu____14705 =
                 let uu____14706 = FStar_Syntax_Subst.compress k  in
                 uu____14706.FStar_Syntax_Syntax.n  in
               match uu____14705 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____14741 -> (tps, k)  in
             match uu____14700 with
             | (formals,res) ->
                 let uu____14748 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____14748 with
                  | (formals1,res1) ->
                      let uu____14759 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____14759 with
                       | (vars,guards,env',binder_decls,uu____14784) ->
                           let arity = FStar_List.length vars  in
                           let uu____14798 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____14798 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____14828 =
                                    let uu____14836 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____14836)  in
                                  FStar_SMTEncoding_Util.mkApp uu____14828
                                   in
                                let uu____14842 =
                                  let tname_decl =
                                    let uu____14852 =
                                      let uu____14853 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____14872 =
                                                  let uu____14874 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____14874
                                                   in
                                                let uu____14876 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____14872, uu____14876,
                                                  false)))
                                         in
                                      let uu____14880 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____14853,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____14880, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____14852
                                     in
                                  let uu____14888 =
                                    match vars with
                                    | [] ->
                                        let uu____14901 =
                                          let uu____14902 =
                                            let uu____14905 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_3  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_3) uu____14905
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____14902
                                           in
                                        ([], uu____14901)
                                    | uu____14917 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____14927 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____14927
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____14943 =
                                            let uu____14951 =
                                              let uu____14952 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____14953 =
                                                let uu____14969 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____14969)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____14952 uu____14953
                                               in
                                            (uu____14951,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____14943
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____14888 with
                                  | (tok_decls,env2) ->
                                      let uu____14996 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____14996
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____14842 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____15024 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____15024 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____15046 =
                                                 let uu____15047 =
                                                   let uu____15055 =
                                                     let uu____15056 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____15056
                                                      in
                                                   (uu____15055,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____15047
                                                  in
                                               [uu____15046]
                                             else []  in
                                           let uu____15064 =
                                             let uu____15067 =
                                               let uu____15070 =
                                                 let uu____15073 =
                                                   let uu____15074 =
                                                     let uu____15082 =
                                                       let uu____15083 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____15084 =
                                                         let uu____15095 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____15095)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____15083
                                                         uu____15084
                                                        in
                                                     (uu____15082,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____15074
                                                    in
                                                 [uu____15073]  in
                                               FStar_List.append karr
                                                 uu____15070
                                                in
                                             FStar_All.pipe_right uu____15067
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____15064
                                        in
                                     let aux =
                                       let uu____15114 =
                                         let uu____15117 =
                                           inversion_axioms tapp vars  in
                                         let uu____15120 =
                                           let uu____15123 =
                                             let uu____15126 =
                                               let uu____15127 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____15127 env2
                                                 tapp vars
                                                in
                                             [uu____15126]  in
                                           FStar_All.pipe_right uu____15123
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____15117
                                           uu____15120
                                          in
                                       FStar_List.append kindingAx
                                         uu____15114
                                        in
                                     let g =
                                       let uu____15135 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____15135
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15143,uu____15144,uu____15145,uu____15146,uu____15147)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15155,t,uu____15157,n_tps,uu____15159) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____15169 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____15169 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15217 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15217 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15245 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15245 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15265 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15265 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15344 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15344,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15351 =
                                   let uu____15352 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15352, true)
                                    in
                                 let uu____15360 =
                                   let uu____15367 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15367
                                    in
                                 FStar_All.pipe_right uu____15351 uu____15360
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
                               let uu____15379 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____15379 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15391::uu____15392 ->
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
                                            let uu____15441 =
                                              let uu____15442 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15442]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15441
                                             in
                                          let uu____15468 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15469 =
                                            let uu____15480 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15480)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15468 uu____15469
                                      | uu____15507 -> tok_typing  in
                                    let uu____15518 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15518 with
                                     | (vars',guards',env'',decls_formals,uu____15543)
                                         ->
                                         let uu____15556 =
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
                                         (match uu____15556 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____15586 ->
                                                    let uu____15595 =
                                                      let uu____15596 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____15596
                                                       in
                                                    [uu____15595]
                                                 in
                                              let encode_elim uu____15612 =
                                                let uu____15613 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____15613 with
                                                | (head1,args) ->
                                                    let uu____15664 =
                                                      let uu____15665 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____15665.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____15664 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____15677;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____15678;_},uu____15679)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____15685 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____15685
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
                                                                  | uu____15748
                                                                    ->
                                                                    let uu____15749
                                                                    =
                                                                    let uu____15755
                                                                    =
                                                                    let uu____15757
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15757
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15755)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15749
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15780
                                                                    =
                                                                    let uu____15782
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15782
                                                                     in
                                                                    if
                                                                    uu____15780
                                                                    then
                                                                    let uu____15804
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15804]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____15807
                                                                =
                                                                let uu____15821
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____15878
                                                                     ->
                                                                    fun
                                                                    uu____15879
                                                                     ->
                                                                    match 
                                                                    (uu____15878,
                                                                    uu____15879)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15990
                                                                    =
                                                                    let uu____15998
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15998
                                                                     in
                                                                    (match uu____15990
                                                                    with
                                                                    | 
                                                                    (uu____16012,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16023
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16023
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16028
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16028
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
                                                                  uu____15821
                                                                 in
                                                              (match uu____15807
                                                               with
                                                               | (uu____16049,arg_vars,elim_eqns_or_guards,uu____16052)
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
                                                                    let uu____16079
                                                                    =
                                                                    let uu____16087
                                                                    =
                                                                    let uu____16088
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16089
                                                                    =
                                                                    let uu____16100
                                                                    =
                                                                    let uu____16101
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16101
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16103
                                                                    =
                                                                    let uu____16104
                                                                    =
                                                                    let uu____16109
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16109)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16104
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16100,
                                                                    uu____16103)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16088
                                                                    uu____16089
                                                                     in
                                                                    (uu____16087,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16079
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16124
                                                                    =
                                                                    let uu____16125
                                                                    =
                                                                    let uu____16131
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16131,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16125
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16124
                                                                     in
                                                                    let uu____16134
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16134
                                                                    then
                                                                    let x =
                                                                    let uu____16138
                                                                    =
                                                                    let uu____16144
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16144,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16138
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16149
                                                                    =
                                                                    let uu____16157
                                                                    =
                                                                    let uu____16158
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16159
                                                                    =
                                                                    let uu____16170
                                                                    =
                                                                    let uu____16175
                                                                    =
                                                                    let uu____16178
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16178]
                                                                     in
                                                                    [uu____16175]
                                                                     in
                                                                    let uu____16183
                                                                    =
                                                                    let uu____16184
                                                                    =
                                                                    let uu____16189
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16191
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16189,
                                                                    uu____16191)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16184
                                                                     in
                                                                    (uu____16170,
                                                                    [x],
                                                                    uu____16183)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16158
                                                                    uu____16159
                                                                     in
                                                                    let uu____16212
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16157,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16212)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16149
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16223
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
                                                                    (let uu____16246
                                                                    =
                                                                    let uu____16247
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16247
                                                                    dapp1  in
                                                                    [uu____16246])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16223
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16254
                                                                    =
                                                                    let uu____16262
                                                                    =
                                                                    let uu____16263
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16264
                                                                    =
                                                                    let uu____16275
                                                                    =
                                                                    let uu____16276
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16276
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16278
                                                                    =
                                                                    let uu____16279
                                                                    =
                                                                    let uu____16284
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16284)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16279
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16275,
                                                                    uu____16278)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16263
                                                                    uu____16264
                                                                     in
                                                                    (uu____16262,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16254)
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
                                                         let uu____16303 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16303
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
                                                                  | uu____16366
                                                                    ->
                                                                    let uu____16367
                                                                    =
                                                                    let uu____16373
                                                                    =
                                                                    let uu____16375
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16375
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16373)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16367
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16398
                                                                    =
                                                                    let uu____16400
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16400
                                                                     in
                                                                    if
                                                                    uu____16398
                                                                    then
                                                                    let uu____16422
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16422]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16425
                                                                =
                                                                let uu____16439
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16496
                                                                     ->
                                                                    fun
                                                                    uu____16497
                                                                     ->
                                                                    match 
                                                                    (uu____16496,
                                                                    uu____16497)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16608
                                                                    =
                                                                    let uu____16616
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16616
                                                                     in
                                                                    (match uu____16608
                                                                    with
                                                                    | 
                                                                    (uu____16630,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16641
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16641
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16646
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16646
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
                                                                  uu____16439
                                                                 in
                                                              (match uu____16425
                                                               with
                                                               | (uu____16667,arg_vars,elim_eqns_or_guards,uu____16670)
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
                                                                    let uu____16697
                                                                    =
                                                                    let uu____16705
                                                                    =
                                                                    let uu____16706
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16707
                                                                    =
                                                                    let uu____16718
                                                                    =
                                                                    let uu____16719
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16719
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16721
                                                                    =
                                                                    let uu____16722
                                                                    =
                                                                    let uu____16727
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16727)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16722
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16718,
                                                                    uu____16721)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16706
                                                                    uu____16707
                                                                     in
                                                                    (uu____16705,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16697
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16742
                                                                    =
                                                                    let uu____16743
                                                                    =
                                                                    let uu____16749
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16749,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16743
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16742
                                                                     in
                                                                    let uu____16752
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16752
                                                                    then
                                                                    let x =
                                                                    let uu____16756
                                                                    =
                                                                    let uu____16762
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16762,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16756
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16767
                                                                    =
                                                                    let uu____16775
                                                                    =
                                                                    let uu____16776
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16777
                                                                    =
                                                                    let uu____16788
                                                                    =
                                                                    let uu____16793
                                                                    =
                                                                    let uu____16796
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16796]
                                                                     in
                                                                    [uu____16793]
                                                                     in
                                                                    let uu____16801
                                                                    =
                                                                    let uu____16802
                                                                    =
                                                                    let uu____16807
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16809
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16807,
                                                                    uu____16809)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16802
                                                                     in
                                                                    (uu____16788,
                                                                    [x],
                                                                    uu____16801)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16776
                                                                    uu____16777
                                                                     in
                                                                    let uu____16830
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16775,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16830)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16767
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16841
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
                                                                    (let uu____16864
                                                                    =
                                                                    let uu____16865
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16865
                                                                    dapp1  in
                                                                    [uu____16864])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16841
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16872
                                                                    =
                                                                    let uu____16880
                                                                    =
                                                                    let uu____16881
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16882
                                                                    =
                                                                    let uu____16893
                                                                    =
                                                                    let uu____16894
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16894
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16896
                                                                    =
                                                                    let uu____16897
                                                                    =
                                                                    let uu____16902
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16902)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16897
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16893,
                                                                    uu____16896)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16881
                                                                    uu____16882
                                                                     in
                                                                    (uu____16880,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16872)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____16919 ->
                                                         ((let uu____16921 =
                                                             let uu____16927
                                                               =
                                                               let uu____16929
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____16931
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____16929
                                                                 uu____16931
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____16927)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____16921);
                                                          ([], [])))
                                                 in
                                              let uu____16939 =
                                                encode_elim ()  in
                                              (match uu____16939 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____16965 =
                                                       let uu____16968 =
                                                         let uu____16971 =
                                                           let uu____16974 =
                                                             let uu____16977
                                                               =
                                                               let uu____16980
                                                                 =
                                                                 let uu____16983
                                                                   =
                                                                   let uu____16984
                                                                    =
                                                                    let uu____16996
                                                                    =
                                                                    let uu____16997
                                                                    =
                                                                    let uu____16999
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16999
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____16997
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____16996)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____16984
                                                                    in
                                                                 [uu____16983]
                                                                  in
                                                               FStar_List.append
                                                                 uu____16980
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____16977
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____17010 =
                                                             let uu____17013
                                                               =
                                                               let uu____17016
                                                                 =
                                                                 let uu____17019
                                                                   =
                                                                   let uu____17022
                                                                    =
                                                                    let uu____17025
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____17030
                                                                    =
                                                                    let uu____17033
                                                                    =
                                                                    let uu____17034
                                                                    =
                                                                    let uu____17042
                                                                    =
                                                                    let uu____17043
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17044
                                                                    =
                                                                    let uu____17055
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____17055)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17043
                                                                    uu____17044
                                                                     in
                                                                    (uu____17042,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17034
                                                                     in
                                                                    let uu____17068
                                                                    =
                                                                    let uu____17071
                                                                    =
                                                                    let uu____17072
                                                                    =
                                                                    let uu____17080
                                                                    =
                                                                    let uu____17081
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17082
                                                                    =
                                                                    let uu____17093
                                                                    =
                                                                    let uu____17094
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17094
                                                                    vars'  in
                                                                    let uu____17096
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17093,
                                                                    uu____17096)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17081
                                                                    uu____17082
                                                                     in
                                                                    (uu____17080,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17072
                                                                     in
                                                                    [uu____17071]
                                                                     in
                                                                    uu____17033
                                                                    ::
                                                                    uu____17068
                                                                     in
                                                                    uu____17025
                                                                    ::
                                                                    uu____17030
                                                                     in
                                                                   FStar_List.append
                                                                    uu____17022
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____17019
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____17016
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____17013
                                                              in
                                                           FStar_List.append
                                                             uu____16974
                                                             uu____17010
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____16971
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____16968
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____16965
                                                      in
                                                   let uu____17113 =
                                                     let uu____17114 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17114 g
                                                      in
                                                   (uu____17113, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17148  ->
              fun se  ->
                match uu____17148 with
                | (g,env1) ->
                    let uu____17168 = encode_sigelt env1 se  in
                    (match uu____17168 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17236 =
        match uu____17236 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17273 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.Beta;
                     FStar_TypeChecker_Env.Eager_unfolding;
                     FStar_TypeChecker_Env.Simplify;
                     FStar_TypeChecker_Env.Primops;
                     FStar_TypeChecker_Env.EraseUniverses]
                     env1.FStar_SMTEncoding_Env.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____17281 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17281
                   then
                     let uu____17286 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17288 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17290 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17286 uu____17288 uu____17290
                   else ());
                  (let uu____17295 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17295 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17313 =
                         let uu____17321 =
                           let uu____17323 =
                             let uu____17325 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17325
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17323  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17321
                          in
                       (match uu____17313 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17345 = FStar_Options.log_queries ()
                                 in
                              if uu____17345
                              then
                                let uu____17348 =
                                  let uu____17350 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17352 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17354 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17350 uu____17352 uu____17354
                                   in
                                FStar_Pervasives_Native.Some uu____17348
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17370 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17380 =
                                let uu____17383 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17383  in
                              FStar_List.append uu____17370 uu____17380  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17395,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17415 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17415 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____17436 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____17436 with | (uu____17463,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17516  ->
              match uu____17516 with
              | (l,uu____17525,uu____17526) ->
                  let uu____17529 =
                    let uu____17541 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17541, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17529))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17574  ->
              match uu____17574 with
              | (l,uu____17585,uu____17586) ->
                  let uu____17589 =
                    let uu____17590 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      uu____17590
                     in
                  let uu____17593 =
                    let uu____17596 =
                      let uu____17597 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17597  in
                    [uu____17596]  in
                  uu____17589 :: uu____17593))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17626 =
      let uu____17629 =
        let uu____17630 = FStar_Util.psmap_empty ()  in
        let uu____17645 =
          let uu____17654 = FStar_Util.psmap_empty ()  in (uu____17654, [])
           in
        let uu____17661 =
          let uu____17663 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____17663 FStar_Ident.string_of_lid  in
        let uu____17665 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17630;
          FStar_SMTEncoding_Env.fvar_bindings = uu____17645;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____17661;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____17665
        }  in
      [uu____17629]  in
    FStar_ST.op_Colon_Equals last_env uu____17626
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____17709 = FStar_ST.op_Bang last_env  in
      match uu____17709 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17737 ->
          let uu___40_17740 = e  in
          let uu____17741 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___40_17740.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___40_17740.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___40_17740.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___40_17740.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___40_17740.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___40_17740.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___40_17740.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____17741;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___40_17740.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___40_17740.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____17749 = FStar_ST.op_Bang last_env  in
    match uu____17749 with
    | [] -> failwith "Empty env stack"
    | uu____17776::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____17808  ->
    let uu____17809 = FStar_ST.op_Bang last_env  in
    match uu____17809 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____17869  ->
    let uu____17870 = FStar_ST.op_Bang last_env  in
    match uu____17870 with
    | [] -> failwith "Popping an empty stack"
    | uu____17897::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____17934  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____17987  ->
         let uu____17988 = snapshot_env ()  in
         match uu____17988 with
         | (env_depth,()) ->
             let uu____18010 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____18010 with
              | (varops_depth,()) ->
                  let uu____18032 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____18032 with
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
        (fun uu____18090  ->
           let uu____18091 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18091 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18186 = snapshot msg  in () 
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
        | (uu____18232::uu____18233,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___41_18241 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___41_18241.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___41_18241.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___41_18241.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18242 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___42_18269 = elt  in
        let uu____18270 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___42_18269.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___42_18269.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18270;
          FStar_SMTEncoding_Term.a_names =
            (uu___42_18269.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18290 =
        let uu____18293 =
          let uu____18294 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18294  in
        let uu____18295 = open_fact_db_tags env  in uu____18293 ::
          uu____18295
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18290
  
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
      let uu____18322 = encode_sigelt env se  in
      match uu____18322 with
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
                (let uu____18368 =
                   let uu____18371 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18371
                    in
                 match uu____18368 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18386 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18386
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18416 = FStar_Options.log_queries ()  in
        if uu____18416
        then
          let uu____18421 =
            let uu____18422 =
              let uu____18424 =
                let uu____18426 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18426 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18424  in
            FStar_SMTEncoding_Term.Caption uu____18422  in
          uu____18421 :: decls
        else decls  in
      (let uu____18445 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18445
       then
         let uu____18448 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18448
       else ());
      (let env =
         let uu____18454 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18454 tcenv  in
       let uu____18455 = encode_top_level_facts env se  in
       match uu____18455 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18469 =
               let uu____18472 =
                 let uu____18475 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18475
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18472  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18469)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18508 = FStar_Options.log_queries ()  in
          if uu____18508
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___43_18528 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___43_18528.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___43_18528.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___43_18528.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___43_18528.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___43_18528.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___43_18528.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___43_18528.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___43_18528.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___43_18528.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___43_18528.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18533 =
             let uu____18536 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18536
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18533  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18556 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18556
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
          (let uu____18580 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____18580
           then
             let uu____18583 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____18583
           else ());
          (let env =
             let uu____18591 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____18591
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____18630  ->
                     fun se  ->
                       match uu____18630 with
                       | (g,env2) ->
                           let uu____18650 = encode_top_level_facts env2 se
                              in
                           (match uu____18650 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____18673 =
             encode_signature
               (let uu___44_18682 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___44_18682.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___44_18682.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___44_18682.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___44_18682.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___44_18682.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___44_18682.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___44_18682.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___44_18682.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___44_18682.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___44_18682.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____18673 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____18698 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18698
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____18704 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____18704))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____18732  ->
        match uu____18732 with
        | (decls,fvbs) ->
            ((let uu____18746 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____18746
              then ()
              else
                (let uu____18751 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18751
                 then
                   let uu____18754 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____18754
                 else ()));
             (let env =
                let uu____18762 = get_env name tcenv  in
                FStar_All.pipe_right uu____18762
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____18764 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____18764
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____18778 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____18778
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
        (let uu____18840 =
           let uu____18842 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____18842.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____18840);
        (let env =
           let uu____18844 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____18844 tcenv  in
         let uu____18845 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____18884 = aux rest  in
                 (match uu____18884 with
                  | (out,rest1) ->
                      let t =
                        let uu____18912 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____18912 with
                        | FStar_Pervasives_Native.Some uu____18915 ->
                            let uu____18916 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____18916
                              x.FStar_Syntax_Syntax.sort
                        | uu____18917 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____18921 =
                        let uu____18924 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___45_18927 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___45_18927.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___45_18927.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____18924 :: out  in
                      (uu____18921, rest1))
             | uu____18932 -> ([], bindings)  in
           let uu____18939 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____18939 with
           | (closing,bindings) ->
               let uu____18966 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____18966, bindings)
            in
         match uu____18845 with
         | (q1,bindings) ->
             let uu____18997 = encode_env_bindings env bindings  in
             (match uu____18997 with
              | (env_decls,env1) ->
                  ((let uu____19019 =
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
                    if uu____19019
                    then
                      let uu____19026 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____19026
                    else ());
                   (let uu____19031 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____19031 with
                    | (phi,qdecls) ->
                        let uu____19052 =
                          let uu____19057 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19057 phi
                           in
                        (match uu____19052 with
                         | (labels,phi1) ->
                             let uu____19074 = encode_labels labels  in
                             (match uu____19074 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19110 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19110
                                    then
                                      let uu____19115 =
                                        let uu____19116 =
                                          let uu____19118 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____19118
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19116
                                         in
                                      [uu____19115]
                                    else []  in
                                  let query_prelude =
                                    let uu____19126 =
                                      let uu____19127 =
                                        let uu____19128 =
                                          let uu____19131 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19138 =
                                            let uu____19141 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19141
                                             in
                                          FStar_List.append uu____19131
                                            uu____19138
                                           in
                                        FStar_List.append env_decls
                                          uu____19128
                                         in
                                      FStar_All.pipe_right uu____19127
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19126
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19151 =
                                      let uu____19159 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19160 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19159,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19160)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19151
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
  