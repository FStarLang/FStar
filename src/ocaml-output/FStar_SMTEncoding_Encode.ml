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
  let uu____136 =
    FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____136 with
  | (asym,a) ->
      let uu____147 =
        FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____147 with
       | (xsym,x) ->
           let uu____158 =
             FStar_SMTEncoding_Env.fresh_fvar "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____158 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____236 =
                      let uu____248 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____248, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____236  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____268 =
                      let uu____276 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____276)  in
                    FStar_SMTEncoding_Util.mkApp uu____268  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____295 =
                    let uu____298 =
                      let uu____301 =
                        let uu____304 =
                          let uu____305 =
                            let uu____313 =
                              let uu____314 =
                                let uu____325 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____325)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____314
                               in
                            (uu____313, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____305  in
                        let uu____337 =
                          let uu____340 =
                            let uu____341 =
                              let uu____349 =
                                let uu____350 =
                                  let uu____361 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____361)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____350
                                 in
                              (uu____349,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____341  in
                          [uu____340]  in
                        uu____304 :: uu____337  in
                      xtok_decl :: uu____301  in
                    xname_decl :: uu____298  in
                  (xtok1, (FStar_List.length vars), uu____295)  in
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
                  let uu____531 =
                    let uu____552 =
                      let uu____571 =
                        let uu____572 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____572
                         in
                      quant axy uu____571  in
                    (FStar_Parser_Const.op_Eq, uu____552)  in
                  let uu____589 =
                    let uu____612 =
                      let uu____633 =
                        let uu____652 =
                          let uu____653 =
                            let uu____654 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____654  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____653
                           in
                        quant axy uu____652  in
                      (FStar_Parser_Const.op_notEq, uu____633)  in
                    let uu____671 =
                      let uu____694 =
                        let uu____715 =
                          let uu____734 =
                            let uu____735 =
                              let uu____736 =
                                let uu____741 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____742 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____741, uu____742)  in
                              FStar_SMTEncoding_Util.mkAnd uu____736  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____735
                             in
                          quant xy uu____734  in
                        (FStar_Parser_Const.op_And, uu____715)  in
                      let uu____759 =
                        let uu____782 =
                          let uu____803 =
                            let uu____822 =
                              let uu____823 =
                                let uu____824 =
                                  let uu____829 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____830 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____829, uu____830)  in
                                FStar_SMTEncoding_Util.mkOr uu____824  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____823
                               in
                            quant xy uu____822  in
                          (FStar_Parser_Const.op_Or, uu____803)  in
                        let uu____847 =
                          let uu____870 =
                            let uu____891 =
                              let uu____910 =
                                let uu____911 =
                                  let uu____912 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____912  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____911
                                 in
                              quant qx uu____910  in
                            (FStar_Parser_Const.op_Negation, uu____891)  in
                          let uu____929 =
                            let uu____952 =
                              let uu____973 =
                                let uu____992 =
                                  let uu____993 =
                                    let uu____994 =
                                      let uu____999 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1000 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____999, uu____1000)  in
                                    FStar_SMTEncoding_Util.mkLT uu____994  in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____993
                                   in
                                quant xy uu____992  in
                              (FStar_Parser_Const.op_LT, uu____973)  in
                            let uu____1017 =
                              let uu____1040 =
                                let uu____1061 =
                                  let uu____1080 =
                                    let uu____1081 =
                                      let uu____1082 =
                                        let uu____1087 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1088 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1087, uu____1088)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1082
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1081
                                     in
                                  quant xy uu____1080  in
                                (FStar_Parser_Const.op_LTE, uu____1061)  in
                              let uu____1105 =
                                let uu____1128 =
                                  let uu____1149 =
                                    let uu____1168 =
                                      let uu____1169 =
                                        let uu____1170 =
                                          let uu____1175 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1176 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1175, uu____1176)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1170
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1169
                                       in
                                    quant xy uu____1168  in
                                  (FStar_Parser_Const.op_GT, uu____1149)  in
                                let uu____1193 =
                                  let uu____1216 =
                                    let uu____1237 =
                                      let uu____1256 =
                                        let uu____1257 =
                                          let uu____1258 =
                                            let uu____1263 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1264 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1263, uu____1264)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1258
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1257
                                         in
                                      quant xy uu____1256  in
                                    (FStar_Parser_Const.op_GTE, uu____1237)
                                     in
                                  let uu____1281 =
                                    let uu____1304 =
                                      let uu____1325 =
                                        let uu____1344 =
                                          let uu____1345 =
                                            let uu____1346 =
                                              let uu____1351 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1352 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1351, uu____1352)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1346
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1345
                                           in
                                        quant xy uu____1344  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1325)
                                       in
                                    let uu____1369 =
                                      let uu____1392 =
                                        let uu____1413 =
                                          let uu____1432 =
                                            let uu____1433 =
                                              let uu____1434 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1434
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1433
                                             in
                                          quant qx uu____1432  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1413)
                                         in
                                      let uu____1451 =
                                        let uu____1474 =
                                          let uu____1495 =
                                            let uu____1514 =
                                              let uu____1515 =
                                                let uu____1516 =
                                                  let uu____1521 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1522 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1521, uu____1522)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1516
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1515
                                               in
                                            quant xy uu____1514  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1495)
                                           in
                                        let uu____1539 =
                                          let uu____1562 =
                                            let uu____1583 =
                                              let uu____1602 =
                                                let uu____1603 =
                                                  let uu____1604 =
                                                    let uu____1609 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____1610 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____1609, uu____1610)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____1604
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____1603
                                                 in
                                              quant xy uu____1602  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____1583)
                                             in
                                          let uu____1627 =
                                            let uu____1650 =
                                              let uu____1671 =
                                                let uu____1690 =
                                                  let uu____1691 =
                                                    let uu____1692 =
                                                      let uu____1697 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____1698 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____1697,
                                                        uu____1698)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____1692
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____1691
                                                   in
                                                quant xy uu____1690  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____1671)
                                               in
                                            let uu____1715 =
                                              let uu____1738 =
                                                let uu____1759 =
                                                  let uu____1778 =
                                                    let uu____1779 =
                                                      let uu____1780 =
                                                        let uu____1785 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____1786 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____1785,
                                                          uu____1786)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____1780
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____1779
                                                     in
                                                  quant xy uu____1778  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____1759)
                                                 in
                                              let uu____1803 =
                                                let uu____1826 =
                                                  let uu____1847 =
                                                    let uu____1866 =
                                                      let uu____1867 =
                                                        let uu____1868 =
                                                          let uu____1873 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____1874 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____1873,
                                                            uu____1874)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____1868
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____1867
                                                       in
                                                    quant xy uu____1866  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____1847)
                                                   in
                                                let uu____1891 =
                                                  let uu____1914 =
                                                    let uu____1935 =
                                                      let uu____1954 =
                                                        let uu____1955 =
                                                          let uu____1956 =
                                                            let uu____1961 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____1962 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____1961,
                                                              uu____1962)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____1956
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____1955
                                                         in
                                                      quant xy uu____1954  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____1935)
                                                     in
                                                  let uu____1979 =
                                                    let uu____2002 =
                                                      let uu____2023 =
                                                        let uu____2042 =
                                                          let uu____2043 =
                                                            let uu____2044 =
                                                              let uu____2049
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2050
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2049,
                                                                uu____2050)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2044
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2043
                                                           in
                                                        quant xy uu____2042
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2023)
                                                       in
                                                    let uu____2067 =
                                                      let uu____2090 =
                                                        let uu____2111 =
                                                          let uu____2130 =
                                                            let uu____2131 =
                                                              let uu____2132
                                                                =
                                                                let uu____2137
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2138
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2137,
                                                                  uu____2138)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2132
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2131
                                                             in
                                                          quant xy uu____2130
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2111)
                                                         in
                                                      let uu____2155 =
                                                        let uu____2178 =
                                                          let uu____2199 =
                                                            let uu____2218 =
                                                              let uu____2219
                                                                =
                                                                let uu____2220
                                                                  =
                                                                  let uu____2225
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2226
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2225,
                                                                    uu____2226)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2220
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2219
                                                               in
                                                            quant xy
                                                              uu____2218
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2199)
                                                           in
                                                        let uu____2243 =
                                                          let uu____2266 =
                                                            let uu____2287 =
                                                              let uu____2306
                                                                =
                                                                let uu____2307
                                                                  =
                                                                  let uu____2308
                                                                    =
                                                                    let uu____2313
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2314
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2313,
                                                                    uu____2314)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2308
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2307
                                                                 in
                                                              quant xy
                                                                uu____2306
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2287)
                                                             in
                                                          let uu____2331 =
                                                            let uu____2354 =
                                                              let uu____2375
                                                                =
                                                                let uu____2394
                                                                  =
                                                                  let uu____2395
                                                                    =
                                                                    let uu____2396
                                                                    =
                                                                    let uu____2401
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2402
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2401,
                                                                    uu____2402)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2396
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2395
                                                                   in
                                                                quant xy
                                                                  uu____2394
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2375)
                                                               in
                                                            let uu____2419 =
                                                              let uu____2442
                                                                =
                                                                let uu____2463
                                                                  =
                                                                  let uu____2482
                                                                    =
                                                                    let uu____2483
                                                                    =
                                                                    let uu____2484
                                                                    =
                                                                    let uu____2489
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2490
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2489,
                                                                    uu____2490)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkDiv
                                                                    uu____2484
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2483
                                                                     in
                                                                  quant xy
                                                                    uu____2482
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2463)
                                                                 in
                                                              let uu____2507
                                                                =
                                                                let uu____2530
                                                                  =
                                                                  let uu____2551
                                                                    =
                                                                    let uu____2570
                                                                    =
                                                                    let uu____2571
                                                                    =
                                                                    let uu____2572
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____2572
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2571
                                                                     in
                                                                    quant qx
                                                                    uu____2570
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____2551)
                                                                   in
                                                                [uu____2530]
                                                                 in
                                                              uu____2442 ::
                                                                uu____2507
                                                               in
                                                            uu____2354 ::
                                                              uu____2419
                                                             in
                                                          uu____2266 ::
                                                            uu____2331
                                                           in
                                                        uu____2178 ::
                                                          uu____2243
                                                         in
                                                      uu____2090 ::
                                                        uu____2155
                                                       in
                                                    uu____2002 :: uu____2067
                                                     in
                                                  uu____1914 :: uu____1979
                                                   in
                                                uu____1826 :: uu____1891  in
                                              uu____1738 :: uu____1803  in
                                            uu____1650 :: uu____1715  in
                                          uu____1562 :: uu____1627  in
                                        uu____1474 :: uu____1539  in
                                      uu____1392 :: uu____1451  in
                                    uu____1304 :: uu____1369  in
                                  uu____1216 :: uu____1281  in
                                uu____1128 :: uu____1193  in
                              uu____1040 :: uu____1105  in
                            uu____952 :: uu____1017  in
                          uu____870 :: uu____929  in
                        uu____782 :: uu____847  in
                      uu____694 :: uu____759  in
                    uu____612 :: uu____671  in
                  uu____531 :: uu____589  in
                let mk1 l v1 =
                  let uu____3111 =
                    let uu____3123 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____3213  ->
                              match uu____3213 with
                              | (l',uu____3234) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3123
                      (FStar_Option.map
                         (fun uu____3333  ->
                            match uu____3333 with
                            | (uu____3361,b) ->
                                let uu____3395 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3395 v1))
                     in
                  FStar_All.pipe_right uu____3111 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____3478  ->
                          match uu____3478 with
                          | (l',uu____3499) -> FStar_Ident.lid_equals l l'))
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
          let uu____3573 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3573 with
          | (xxsym,xx) ->
              let uu____3584 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____3584 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____3600 =
                     let uu____3608 =
                       let uu____3609 =
                         let uu____3620 =
                           let uu____3621 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____3631 =
                             let uu____3642 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____3642 :: vars  in
                           uu____3621 :: uu____3631  in
                         let uu____3668 =
                           let uu____3669 =
                             let uu____3674 =
                               let uu____3675 =
                                 let uu____3680 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3680)  in
                               FStar_SMTEncoding_Util.mkEq uu____3675  in
                             (xx_has_type, uu____3674)  in
                           FStar_SMTEncoding_Util.mkImp uu____3669  in
                         ([[xx_has_type]], uu____3620, uu____3668)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____3609  in
                     let uu____3693 =
                       let uu____3695 =
                         let uu____3697 =
                           let uu____3699 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____3699  in
                         Prims.strcat module_name uu____3697  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3695
                        in
                     (uu____3608, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3693)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____3600)
  
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
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3752 =
      let uu____3753 =
        let uu____3761 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3761, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3753  in
    let uu____3766 =
      let uu____3769 =
        let uu____3770 =
          let uu____3778 =
            let uu____3779 =
              let uu____3790 =
                let uu____3791 =
                  let uu____3796 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3796)  in
                FStar_SMTEncoding_Util.mkImp uu____3791  in
              ([[typing_pred]], [xx], uu____3790)  in
            let uu____3821 =
              let uu____3836 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3836  in
            uu____3821 uu____3779  in
          (uu____3778, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3770  in
      [uu____3769]  in
    uu____3752 :: uu____3766  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3864 =
      let uu____3865 =
        let uu____3873 =
          let uu____3874 = FStar_TypeChecker_Env.get_range env  in
          let uu____3875 =
            let uu____3886 =
              let uu____3891 =
                let uu____3894 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3894]  in
              [uu____3891]  in
            let uu____3899 =
              let uu____3900 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3900 tt  in
            (uu____3886, [bb], uu____3899)  in
          FStar_SMTEncoding_Term.mkForall uu____3874 uu____3875  in
        (uu____3873, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3865  in
    let uu____3925 =
      let uu____3928 =
        let uu____3929 =
          let uu____3937 =
            let uu____3938 =
              let uu____3949 =
                let uu____3950 =
                  let uu____3955 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____3955)  in
                FStar_SMTEncoding_Util.mkImp uu____3950  in
              ([[typing_pred]], [xx], uu____3949)  in
            let uu____3982 =
              let uu____3997 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3997  in
            uu____3982 uu____3938  in
          (uu____3937, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3929  in
      [uu____3928]  in
    uu____3864 :: uu____3925  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____4021 =
        let uu____4022 =
          let uu____4028 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4028, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4022  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4021  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4042 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4042  in
    let uu____4047 =
      let uu____4048 =
        let uu____4056 =
          let uu____4057 = FStar_TypeChecker_Env.get_range env  in
          let uu____4058 =
            let uu____4069 =
              let uu____4074 =
                let uu____4077 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4077]  in
              [uu____4074]  in
            let uu____4082 =
              let uu____4083 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4083 tt  in
            (uu____4069, [bb], uu____4082)  in
          FStar_SMTEncoding_Term.mkForall uu____4057 uu____4058  in
        (uu____4056, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4048  in
    let uu____4108 =
      let uu____4111 =
        let uu____4112 =
          let uu____4120 =
            let uu____4121 =
              let uu____4132 =
                let uu____4133 =
                  let uu____4138 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4138)  in
                FStar_SMTEncoding_Util.mkImp uu____4133  in
              ([[typing_pred]], [xx], uu____4132)  in
            let uu____4165 =
              let uu____4180 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4180  in
            uu____4165 uu____4121  in
          (uu____4120, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4112  in
      let uu____4185 =
        let uu____4188 =
          let uu____4189 =
            let uu____4197 =
              let uu____4198 =
                let uu____4209 =
                  let uu____4210 =
                    let uu____4215 =
                      let uu____4216 =
                        let uu____4219 =
                          let uu____4222 =
                            let uu____4225 =
                              let uu____4226 =
                                let uu____4231 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4232 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____4231, uu____4232)  in
                              FStar_SMTEncoding_Util.mkGT uu____4226  in
                            let uu____4234 =
                              let uu____4237 =
                                let uu____4238 =
                                  let uu____4243 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4244 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____4243, uu____4244)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4238  in
                              let uu____4246 =
                                let uu____4249 =
                                  let uu____4250 =
                                    let uu____4255 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4256 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4255, uu____4256)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4250  in
                                [uu____4249]  in
                              uu____4237 :: uu____4246  in
                            uu____4225 :: uu____4234  in
                          typing_pred_y :: uu____4222  in
                        typing_pred :: uu____4219  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4216  in
                    (uu____4215, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4210  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4209)
                 in
              let uu____4289 =
                let uu____4304 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4304  in
              uu____4289 uu____4198  in
            (uu____4197,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4189  in
        [uu____4188]  in
      uu____4111 :: uu____4185  in
    uu____4047 :: uu____4108  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____4328 =
        let uu____4329 =
          let uu____4335 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4335, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4329  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4328  in
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
      let uu____4351 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4351  in
    let uu____4356 =
      let uu____4357 =
        let uu____4365 =
          let uu____4366 = FStar_TypeChecker_Env.get_range env  in
          let uu____4367 =
            let uu____4378 =
              let uu____4383 =
                let uu____4386 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4386]  in
              [uu____4383]  in
            let uu____4391 =
              let uu____4392 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4392 tt  in
            (uu____4378, [bb], uu____4391)  in
          FStar_SMTEncoding_Term.mkForall uu____4366 uu____4367  in
        (uu____4365, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4357  in
    let uu____4417 =
      let uu____4420 =
        let uu____4421 =
          let uu____4429 =
            let uu____4430 =
              let uu____4441 =
                let uu____4442 =
                  let uu____4447 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____4447)  in
                FStar_SMTEncoding_Util.mkImp uu____4442  in
              ([[typing_pred]], [xx], uu____4441)  in
            let uu____4474 =
              let uu____4489 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4489  in
            uu____4474 uu____4430  in
          (uu____4429, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4421  in
      let uu____4494 =
        let uu____4497 =
          let uu____4498 =
            let uu____4506 =
              let uu____4507 =
                let uu____4518 =
                  let uu____4519 =
                    let uu____4524 =
                      let uu____4525 =
                        let uu____4528 =
                          let uu____4531 =
                            let uu____4534 =
                              let uu____4535 =
                                let uu____4540 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____4541 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____4540, uu____4541)  in
                              FStar_SMTEncoding_Util.mkGT uu____4535  in
                            let uu____4543 =
                              let uu____4546 =
                                let uu____4547 =
                                  let uu____4552 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____4553 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____4552, uu____4553)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4547  in
                              let uu____4555 =
                                let uu____4558 =
                                  let uu____4559 =
                                    let uu____4564 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____4565 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____4564, uu____4565)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4559  in
                                [uu____4558]  in
                              uu____4546 :: uu____4555  in
                            uu____4534 :: uu____4543  in
                          typing_pred_y :: uu____4531  in
                        typing_pred :: uu____4528  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4525  in
                    (uu____4524, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4519  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4518)
                 in
              let uu____4598 =
                let uu____4613 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4613  in
              uu____4598 uu____4507  in
            (uu____4506,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4498  in
        [uu____4497]  in
      uu____4420 :: uu____4494  in
    uu____4356 :: uu____4417  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4641 =
      let uu____4642 =
        let uu____4650 =
          let uu____4651 = FStar_TypeChecker_Env.get_range env  in
          let uu____4652 =
            let uu____4663 =
              let uu____4668 =
                let uu____4671 = FStar_SMTEncoding_Term.boxString b  in
                [uu____4671]  in
              [uu____4668]  in
            let uu____4676 =
              let uu____4677 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4677 tt  in
            (uu____4663, [bb], uu____4676)  in
          FStar_SMTEncoding_Term.mkForall uu____4651 uu____4652  in
        (uu____4650, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4642  in
    let uu____4702 =
      let uu____4705 =
        let uu____4706 =
          let uu____4714 =
            let uu____4715 =
              let uu____4726 =
                let uu____4727 =
                  let uu____4732 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____4732)  in
                FStar_SMTEncoding_Util.mkImp uu____4727  in
              ([[typing_pred]], [xx], uu____4726)  in
            let uu____4759 =
              let uu____4774 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4774  in
            uu____4759 uu____4715  in
          (uu____4714, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4706  in
      [uu____4705]  in
    uu____4641 :: uu____4702  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____4802 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____4802]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____4830 =
      let uu____4831 =
        let uu____4839 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____4839, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4831  in
    [uu____4830]  in
  let mk_and_interp env conj uu____4860 =
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
    let uu____4889 =
      let uu____4890 =
        let uu____4898 =
          let uu____4899 = FStar_TypeChecker_Env.get_range env  in
          let uu____4900 =
            let uu____4911 =
              let uu____4912 =
                let uu____4917 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____4917, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4912  in
            ([[l_and_a_b]], [aa; bb], uu____4911)  in
          FStar_SMTEncoding_Term.mkForall uu____4899 uu____4900  in
        (uu____4898, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4890  in
    [uu____4889]  in
  let mk_or_interp env disj uu____4970 =
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
    let uu____4999 =
      let uu____5000 =
        let uu____5008 =
          let uu____5009 = FStar_TypeChecker_Env.get_range env  in
          let uu____5010 =
            let uu____5021 =
              let uu____5022 =
                let uu____5027 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5027, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5022  in
            ([[l_or_a_b]], [aa; bb], uu____5021)  in
          FStar_SMTEncoding_Term.mkForall uu____5009 uu____5010  in
        (uu____5008, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5000  in
    [uu____4999]  in
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
    let uu____5103 =
      let uu____5104 =
        let uu____5112 =
          let uu____5113 = FStar_TypeChecker_Env.get_range env  in
          let uu____5114 =
            let uu____5125 =
              let uu____5126 =
                let uu____5131 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5131, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5126  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5125)  in
          FStar_SMTEncoding_Term.mkForall uu____5113 uu____5114  in
        (uu____5112, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5104  in
    [uu____5103]  in
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
    let uu____5219 =
      let uu____5220 =
        let uu____5228 =
          let uu____5229 = FStar_TypeChecker_Env.get_range env  in
          let uu____5230 =
            let uu____5241 =
              let uu____5242 =
                let uu____5247 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5247, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5242  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5241)  in
          FStar_SMTEncoding_Term.mkForall uu____5229 uu____5230  in
        (uu____5228, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5220  in
    [uu____5219]  in
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
    let uu____5345 =
      let uu____5346 =
        let uu____5354 =
          let uu____5355 = FStar_TypeChecker_Env.get_range env  in
          let uu____5356 =
            let uu____5367 =
              let uu____5368 =
                let uu____5373 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____5373, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5368  in
            ([[l_imp_a_b]], [aa; bb], uu____5367)  in
          FStar_SMTEncoding_Term.mkForall uu____5355 uu____5356  in
        (uu____5354, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5346  in
    [uu____5345]  in
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
    let uu____5455 =
      let uu____5456 =
        let uu____5464 =
          let uu____5465 = FStar_TypeChecker_Env.get_range env  in
          let uu____5466 =
            let uu____5477 =
              let uu____5478 =
                let uu____5483 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____5483, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5478  in
            ([[l_iff_a_b]], [aa; bb], uu____5477)  in
          FStar_SMTEncoding_Term.mkForall uu____5465 uu____5466  in
        (uu____5464, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5456  in
    [uu____5455]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____5552 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____5552  in
    let uu____5557 =
      let uu____5558 =
        let uu____5566 =
          let uu____5567 = FStar_TypeChecker_Env.get_range env  in
          let uu____5568 =
            let uu____5579 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____5579)  in
          FStar_SMTEncoding_Term.mkForall uu____5567 uu____5568  in
        (uu____5566, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5558  in
    [uu____5557]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____5630 =
      let uu____5631 =
        let uu____5639 =
          let uu____5640 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____5640 range_ty  in
        let uu____5641 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____5639, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____5641)
         in
      FStar_SMTEncoding_Util.mkAssume uu____5631  in
    [uu____5630]  in
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
        let uu____5685 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____5685 x1 t  in
      let uu____5687 = FStar_TypeChecker_Env.get_range env  in
      let uu____5688 =
        let uu____5699 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____5699)  in
      FStar_SMTEncoding_Term.mkForall uu____5687 uu____5688  in
    let uu____5724 =
      let uu____5725 =
        let uu____5733 =
          let uu____5734 = FStar_TypeChecker_Env.get_range env  in
          let uu____5735 =
            let uu____5746 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____5746)  in
          FStar_SMTEncoding_Term.mkForall uu____5734 uu____5735  in
        (uu____5733,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5725  in
    [uu____5724]  in
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
    let uu____5805 =
      let uu____5806 =
        let uu____5814 =
          let uu____5815 = FStar_TypeChecker_Env.get_range env  in
          let uu____5816 =
            let uu____5832 =
              let uu____5833 =
                let uu____5838 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____5839 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____5838, uu____5839)  in
              FStar_SMTEncoding_Util.mkAnd uu____5833  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____5832)
             in
          FStar_SMTEncoding_Term.mkForall' uu____5815 uu____5816  in
        (uu____5814,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5806  in
    [uu____5805]  in
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
          let uu____6397 =
            FStar_Util.find_opt
              (fun uu____6435  ->
                 match uu____6435 with
                 | (l,uu____6451) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____6397 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____6494,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____6555 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____6555 with
        | (form,decls) ->
            let uu____6564 =
              let uu____6567 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____6567]  in
            FStar_List.append decls uu____6564
  
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list *
                FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____6620 =
                ((let uu____6624 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____6624) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____6620
              then
                let arg_sorts =
                  let uu____6638 =
                    let uu____6639 = FStar_Syntax_Subst.compress t_norm  in
                    uu____6639.FStar_Syntax_Syntax.n  in
                  match uu____6638 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6645) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6683  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6690 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6692 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6692 with
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
                    ([d; dd], env1)
              else
                (let uu____6734 = prims.is lid  in
                 if uu____6734
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6745 = prims.mk lid vname  in
                   match uu____6745 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6779 =
                      let uu____6798 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____6798 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____6826 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____6826
                            then
                              let uu____6831 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___383_6834 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___383_6834.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___383_6834.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___383_6834.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___383_6834.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___383_6834.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___383_6834.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___383_6834.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___383_6834.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___383_6834.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___383_6834.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___383_6834.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___383_6834.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___383_6834.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___383_6834.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___383_6834.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___383_6834.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___383_6834.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___383_6834.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___383_6834.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___383_6834.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___383_6834.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___383_6834.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___383_6834.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___383_6834.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___383_6834.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___383_6834.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___383_6834.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___383_6834.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___383_6834.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___383_6834.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___383_6834.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___383_6834.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___383_6834.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___383_6834.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___383_6834.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___383_6834.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___383_6834.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___383_6834.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___383_6834.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___383_6834.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___383_6834.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___383_6834.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____6831
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____6857 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____6857)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6779 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___373_6965  ->
                                  match uu___373_6965 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____6969 = FStar_Util.prefix vars
                                         in
                                      (match uu____6969 with
                                       | (uu____7002,xxv) ->
                                           let xx =
                                             let uu____7041 =
                                               let uu____7042 =
                                                 let uu____7048 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7048,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7042
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7041
                                              in
                                           let uu____7051 =
                                             let uu____7052 =
                                               let uu____7060 =
                                                 let uu____7061 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7062 =
                                                   let uu____7073 =
                                                     let uu____7074 =
                                                       let uu____7079 =
                                                         let uu____7080 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7080
                                                          in
                                                       (vapp, uu____7079)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7074
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7073)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7061 uu____7062
                                                  in
                                               (uu____7060,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.strcat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7052
                                              in
                                           [uu____7051])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7095 = FStar_Util.prefix vars
                                         in
                                      (match uu____7095 with
                                       | (uu____7128,xxv) ->
                                           let xx =
                                             let uu____7167 =
                                               let uu____7168 =
                                                 let uu____7174 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7174,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7168
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7167
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
                                           let uu____7185 =
                                             let uu____7186 =
                                               let uu____7194 =
                                                 let uu____7195 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7196 =
                                                   let uu____7207 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7207)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7195 uu____7196
                                                  in
                                               (uu____7194,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.strcat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7186
                                              in
                                           [uu____7185])
                                  | uu____7220 -> []))
                           in
                        let uu____7221 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7221 with
                         | (vars,guards,env',decls1,uu____7248) ->
                             let uu____7261 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7274 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7274, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7278 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7278 with
                                    | (g,ds) ->
                                        let uu____7291 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7291,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7261 with
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
                                  let should_thunk uu____7316 =
                                    let is_type1 t =
                                      let uu____7324 =
                                        let uu____7325 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7325.FStar_Syntax_Syntax.n  in
                                      match uu____7324 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7329 -> true
                                      | uu____7331 -> false  in
                                    let is_squash1 t =
                                      let uu____7340 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____7340 with
                                      | (head1,uu____7359) ->
                                          let uu____7384 =
                                            let uu____7385 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____7385.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7384 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____7390;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____7391;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____7393;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____7394;_};_},uu____7395)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____7403 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____7408 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____7408))
                                       &&
                                       (let uu____7414 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____7414))
                                      &&
                                      (let uu____7417 = is_type1 t_norm  in
                                       Prims.op_Negation uu____7417)
                                     in
                                  let uu____7419 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____7478 -> (false, vars)  in
                                  (match uu____7419 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____7530 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____7530 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____7568 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____7577 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____7577
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____7588 ->
                                                  let uu____7597 =
                                                    let uu____7605 =
                                                      get_vtok ()  in
                                                    (uu____7605, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7597
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____7612 =
                                                let uu____7620 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____7620)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____7612
                                               in
                                            let uu____7634 =
                                              let vname_decl =
                                                let uu____7642 =
                                                  let uu____7654 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____7654,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____7642
                                                 in
                                              let uu____7665 =
                                                let env2 =
                                                  let uu___384_7671 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.cache
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.cache);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___384_7671.FStar_SMTEncoding_Env.encoding_quantifier)
                                                  }  in
                                                let uu____7672 =
                                                  let uu____7674 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____7674
                                                   in
                                                if uu____7672
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____7665 with
                                              | (tok_typing,decls2) ->
                                                  let uu____7691 =
                                                    match vars1 with
                                                    | [] ->
                                                        let tok_typing1 =
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.strcat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____7717 =
                                                          let uu____7718 =
                                                            let uu____7721 =
                                                              let uu____7722
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____7722
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _0_1  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _0_1)
                                                              uu____7721
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____7718
                                                           in
                                                        ((FStar_List.append
                                                            decls2
                                                            [tok_typing1]),
                                                          uu____7717)
                                                    | uu____7732 when thunked
                                                        ->
                                                        let uu____7743 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____7743
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____7758
                                                                 =
                                                                 let uu____7766
                                                                   =
                                                                   let uu____7769
                                                                    =
                                                                    let uu____7772
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____7772]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____7769
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____7766)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____7758
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____7780 =
                                                               let uu____7788
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____7788,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.strcat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7780
                                                              in
                                                           ((FStar_List.append
                                                               decls2
                                                               [intro_ambient1]),
                                                             env1))
                                                    | uu____7795 ->
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
                                                          let uu____7819 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____7820 =
                                                            let uu____7831 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____7831)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____7819
                                                            uu____7820
                                                           in
                                                        let name_tok_corr =
                                                          let uu____7841 =
                                                            let uu____7849 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____7849,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.strcat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7841
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
                                                            let uu____7860 =
                                                              let uu____7861
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____7861]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____7860
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____7888 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____7889 =
                                                              let uu____7900
                                                                =
                                                                let uu____7901
                                                                  =
                                                                  let uu____7906
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____7907
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____7906,
                                                                    uu____7907)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____7901
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____7900)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____7888
                                                              uu____7889
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.strcat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        ((FStar_List.append
                                                            decls2
                                                            [vtok_decl;
                                                            name_tok_corr;
                                                            tok_typing1]),
                                                          env1)
                                                     in
                                                  (match uu____7691 with
                                                   | (tok_decl,env2) ->
                                                       ((vname_decl ::
                                                         tok_decl), env2))
                                               in
                                            (match uu____7634 with
                                             | (decls2,env2) ->
                                                 let uu____7964 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____7974 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____7974 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____7989 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____7989, decls)
                                                    in
                                                 (match uu____7964 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8006 =
                                                          let uu____8014 =
                                                            let uu____8015 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8016 =
                                                              let uu____8027
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8027)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8015
                                                              uu____8016
                                                             in
                                                          (uu____8014,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.strcat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8006
                                                         in
                                                      let freshness =
                                                        let uu____8043 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8043
                                                        then
                                                          let uu____8051 =
                                                            let uu____8052 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8053 =
                                                              let uu____8066
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8073
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8066,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8073)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8052
                                                              uu____8053
                                                             in
                                                          let uu____8079 =
                                                            let uu____8082 =
                                                              let uu____8083
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8083
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8082]  in
                                                          uu____8051 ::
                                                            uu____8079
                                                        else []  in
                                                      let g =
                                                        let uu____8089 =
                                                          let uu____8092 =
                                                            let uu____8095 =
                                                              let uu____8098
                                                                =
                                                                let uu____8101
                                                                  =
                                                                  mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1
                                                                   in
                                                                typingAx ::
                                                                  uu____8101
                                                                 in
                                                              FStar_List.append
                                                                freshness
                                                                uu____8098
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8095
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8092
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8089
                                                         in
                                                      (g, env2)))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding * FStar_SMTEncoding_Term.decl
            Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____8139 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8139 with
          | FStar_Pervasives_Native.None  ->
              let uu____8150 = encode_free_var false env x t t_norm []  in
              (match uu____8150 with
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
            (FStar_SMTEncoding_Term.decl Prims.list *
              FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = FStar_SMTEncoding_EncodeTerm.norm env t  in
            let uu____8221 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8221 with
            | (decls,env1) ->
                let uu____8240 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8240
                then
                  let uu____8249 =
                    let uu____8252 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8252  in
                  (uu____8249, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____8312  ->
                fun lb  ->
                  match uu____8312 with
                  | (decls,env1) ->
                      let uu____8332 =
                        let uu____8339 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8339
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8332 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8372 = FStar_Syntax_Util.head_and_args t  in
    match uu____8372 with
    | (hd1,args) ->
        let uu____8416 =
          let uu____8417 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8417.FStar_Syntax_Syntax.n  in
        (match uu____8416 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8423,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____8447 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____8458 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___385_8466 = en  in
    let uu____8467 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___385_8466.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___385_8466.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___385_8466.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___385_8466.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___385_8466.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____8467;
      FStar_SMTEncoding_Env.nolabels =
        (uu___385_8466.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___385_8466.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___385_8466.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___385_8466.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___385_8466.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____8499  ->
      fun quals  ->
        match uu____8499 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8606 = FStar_Util.first_N nbinders formals  in
              match uu____8606 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____8707  ->
                         fun uu____8708  ->
                           match (uu____8707, uu____8708) with
                           | ((formal,uu____8734),(binder,uu____8736)) ->
                               let uu____8757 =
                                 let uu____8764 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____8764)  in
                               FStar_Syntax_Syntax.NT uu____8757) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____8778 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8819  ->
                              match uu____8819 with
                              | (x,i) ->
                                  let uu____8838 =
                                    let uu___386_8839 = x  in
                                    let uu____8840 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___386_8839.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___386_8839.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8840
                                    }  in
                                  (uu____8838, i)))
                       in
                    FStar_All.pipe_right uu____8778
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____8864 =
                      let uu____8869 = FStar_Syntax_Subst.compress body  in
                      let uu____8870 =
                        let uu____8871 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____8871
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____8869 uu____8870
                       in
                    uu____8864 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___387_8922 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___387_8922.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___387_8922.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___387_8922.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___387_8922.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___387_8922.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___387_8922.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___387_8922.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___387_8922.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___387_8922.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___387_8922.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___387_8922.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___387_8922.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___387_8922.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___387_8922.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___387_8922.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___387_8922.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___387_8922.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___387_8922.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___387_8922.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___387_8922.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___387_8922.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___387_8922.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___387_8922.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___387_8922.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___387_8922.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___387_8922.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___387_8922.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___387_8922.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___387_8922.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___387_8922.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___387_8922.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___387_8922.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___387_8922.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___387_8922.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___387_8922.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___387_8922.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___387_8922.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___387_8922.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___387_8922.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___387_8922.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___387_8922.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___387_8922.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____8994  ->
                       fun uu____8995  ->
                         match (uu____8994, uu____8995) with
                         | ((x,uu____9021),(b,uu____9023)) ->
                             let uu____9044 =
                               let uu____9051 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9051)  in
                             FStar_Syntax_Syntax.NT uu____9044) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9076 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9076
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9105 ->
                    let uu____9112 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9112
                | uu____9113 when Prims.op_Negation norm1 ->
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
                | uu____9116 ->
                    let uu____9117 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9117)
                 in
              let aux t1 e1 =
                let uu____9159 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9159 with
                | (binders,body,lopt) ->
                    let uu____9191 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9207 -> arrow_formals_comp_norm false t1  in
                    (match uu____9191 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9241 =
                           if nformals < nbinders
                           then
                             let uu____9285 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9285 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9369 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9369)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9409 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9409 with
                                | (binders1,body1) ->
                                    let uu____9462 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____9462))
                             else
                               (let uu____9475 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____9475))
                            in
                         (match uu____9241 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____9535 = aux t e  in
              match uu____9535 with
              | (binders,body,comp) ->
                  let uu____9581 =
                    let uu____9592 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____9592
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____9607 = aux comp1 body1  in
                      match uu____9607 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____9581 with
                   | (binders1,body1,comp1) ->
                       let uu____9690 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____9690, comp1))
               in
            (try
               (fun uu___389_9717  ->
                  match () with
                  | () ->
                      let uu____9724 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9724
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9740 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9803  ->
                                   fun lb  ->
                                     match uu____9803 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9858 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9858
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9864 =
                                             let uu____9873 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9873
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9864 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9740 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10014;
                                    FStar_Syntax_Syntax.lbeff = uu____10015;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10017;
                                    FStar_Syntax_Syntax.lbpos = uu____10018;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10042 =
                                     let uu____10049 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10049 with
                                     | (tcenv',uu____10065,e_t) ->
                                         let uu____10071 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10082 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10071 with
                                          | (e1,t_norm1) ->
                                              ((let uu___390_10099 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___390_10099.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10042 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10109 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10109 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10129 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10129
                                               then
                                                 let uu____10134 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10137 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10134 uu____10137
                                               else ());
                                              (let uu____10142 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10142 with
                                               | (vars,_guards,env'1,binder_decls,uu____10169)
                                                   ->
                                                   let uu____10182 =
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
                                                         let uu____10199 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10199
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10221 =
                                                          let uu____10222 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10223 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10222 fvb
                                                            uu____10223
                                                           in
                                                        (vars, uu____10221))
                                                      in
                                                   (match uu____10182 with
                                                    | (vars1,app) ->
                                                        let uu____10234 =
                                                          let is_logical =
                                                            let uu____10247 =
                                                              let uu____10248
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10248.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10247
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10254 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10258 =
                                                              let uu____10259
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10259
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10258
                                                              (fun lid  ->
                                                                 let uu____10268
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10268
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10269 =
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
                                                          if uu____10269
                                                          then
                                                            let uu____10285 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10286 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10285,
                                                              uu____10286)
                                                          else
                                                            (let uu____10297
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10297))
                                                           in
                                                        (match uu____10234
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10321
                                                                 =
                                                                 let uu____10329
                                                                   =
                                                                   let uu____10330
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10331
                                                                    =
                                                                    let uu____10342
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10342)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10330
                                                                    uu____10331
                                                                    in
                                                                 let uu____10351
                                                                   =
                                                                   let uu____10352
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10352
                                                                    in
                                                                 (uu____10329,
                                                                   uu____10351,
                                                                   (Prims.strcat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10321
                                                                in
                                                             let uu____10358
                                                               =
                                                               let uu____10361
                                                                 =
                                                                 let uu____10364
                                                                   =
                                                                   let uu____10367
                                                                    =
                                                                    let uu____10370
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    FStar_List.append
                                                                    [eqn]
                                                                    uu____10370
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10367
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10364
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10361
                                                                in
                                                             (uu____10358,
                                                               env2)))))))
                               | uu____10375 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10435 =
                                   let uu____10441 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       "fuel"
                                      in
                                   (uu____10441,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10435  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10447 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10500  ->
                                         fun fvb  ->
                                           match uu____10500 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10555 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10555
                                                  in
                                               let gtok =
                                                 let uu____10559 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10559
                                                  in
                                               let env4 =
                                                 let uu____10562 =
                                                   let uu____10565 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____10565
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10562
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10447 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10692
                                     t_norm uu____10694 =
                                     match (uu____10692, uu____10694) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10726;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10727;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10729;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10730;_})
                                         ->
                                         let uu____10757 =
                                           let uu____10764 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10764 with
                                           | (tcenv',uu____10780,e_t) ->
                                               let uu____10786 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10797 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10786 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___391_10814 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___391_10814.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10757 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10829 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10829
                                                then
                                                  let uu____10834 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10836 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10838 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10834 uu____10836
                                                    uu____10838
                                                else ());
                                               (let uu____10843 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____10843 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____10872 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____10872 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____10896 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____10896
                                                           then
                                                             let uu____10901
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____10903
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____10906
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____10908
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____10901
                                                               uu____10903
                                                               uu____10906
                                                               uu____10908
                                                           else ());
                                                          (let uu____10913 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____10913
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____10944)
                                                               ->
                                                               let uu____10957
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____10970
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____10970,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____10974
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____10974
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____10987
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____10987,
                                                                    decls0))
                                                                  in
                                                               (match uu____10957
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
                                                                    let uu____11010
                                                                    =
                                                                    let uu____11022
                                                                    =
                                                                    let uu____11025
                                                                    =
                                                                    let uu____11028
                                                                    =
                                                                    let uu____11031
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11031
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11028
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11025
                                                                     in
                                                                    (g,
                                                                    uu____11022,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11010
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
                                                                    let uu____11061
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11061
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
                                                                    let uu____11076
                                                                    =
                                                                    let uu____11079
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11079
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11076
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11085
                                                                    =
                                                                    let uu____11088
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11088
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11085
                                                                     in
                                                                    let uu____11093
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11093
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11111
                                                                    =
                                                                    let uu____11119
                                                                    =
                                                                    let uu____11120
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11121
                                                                    =
                                                                    let uu____11137
                                                                    =
                                                                    let uu____11138
                                                                    =
                                                                    let uu____11143
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11143)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11138
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11137)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11120
                                                                    uu____11121
                                                                     in
                                                                    let uu____11157
                                                                    =
                                                                    let uu____11158
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11158
                                                                     in
                                                                    (uu____11119,
                                                                    uu____11157,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11111
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11165
                                                                    =
                                                                    let uu____11173
                                                                    =
                                                                    let uu____11174
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11175
                                                                    =
                                                                    let uu____11186
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11186)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11174
                                                                    uu____11175
                                                                     in
                                                                    (uu____11173,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11165
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11200
                                                                    =
                                                                    let uu____11208
                                                                    =
                                                                    let uu____11209
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11210
                                                                    =
                                                                    let uu____11221
                                                                    =
                                                                    let uu____11222
                                                                    =
                                                                    let uu____11227
                                                                    =
                                                                    let uu____11228
                                                                    =
                                                                    let uu____11231
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11231
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11228
                                                                     in
                                                                    (gsapp,
                                                                    uu____11227)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11222
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11221)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11209
                                                                    uu____11210
                                                                     in
                                                                    (uu____11208,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11200
                                                                     in
                                                                    let uu____11245
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
                                                                    let uu____11257
                                                                    =
                                                                    let uu____11258
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11258
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11257
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____11260
                                                                    =
                                                                    let uu____11268
                                                                    =
                                                                    let uu____11269
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11270
                                                                    =
                                                                    let uu____11281
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11281)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11269
                                                                    uu____11270
                                                                     in
                                                                    (uu____11268,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11260
                                                                     in
                                                                    let uu____11294
                                                                    =
                                                                    let uu____11303
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11303
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11318
                                                                    =
                                                                    let uu____11321
                                                                    =
                                                                    let uu____11322
                                                                    =
                                                                    let uu____11330
                                                                    =
                                                                    let uu____11331
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11332
                                                                    =
                                                                    let uu____11343
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11343)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11331
                                                                    uu____11332
                                                                     in
                                                                    (uu____11330,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11322
                                                                     in
                                                                    [uu____11321]
                                                                     in
                                                                    (d3,
                                                                    uu____11318)
                                                                     in
                                                                    match uu____11294
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11245
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    (FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                    env02))))))))))
                                      in
                                   let uu____11406 =
                                     let uu____11419 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11482  ->
                                          fun uu____11483  ->
                                            match (uu____11482, uu____11483)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11608 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11608 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11419
                                      in
                                   (match uu____11406 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11681 =
                                          let isDeclFun uu___374_11696 =
                                            match uu___374_11696 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11698 -> true
                                            | uu____11711 -> false  in
                                          let uu____11713 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11713
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____11681 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____11753 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___375_11759  ->
                                        match uu___375_11759 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____11762 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____11770 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____11770)))
                                in
                             if uu____11753
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___393_11792  ->
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
                   let uu____11830 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____11830
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____11900 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____11900 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____11906 = encode_sigelt' env se  in
      match uu____11906 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____11918 =
                  let uu____11919 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____11919  in
                [uu____11918]
            | uu____11922 ->
                let uu____11923 =
                  let uu____11926 =
                    let uu____11927 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11927  in
                  uu____11926 :: g  in
                let uu____11930 =
                  let uu____11933 =
                    let uu____11934 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11934  in
                  [uu____11933]  in
                FStar_List.append uu____11923 uu____11930
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____11944 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____11944
       then
         let uu____11949 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____11949
       else ());
      (let is_opaque_to_smt t =
         let uu____11961 =
           let uu____11962 = FStar_Syntax_Subst.compress t  in
           uu____11962.FStar_Syntax_Syntax.n  in
         match uu____11961 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____11967)) -> s = "opaque_to_smt"
         | uu____11972 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____11981 =
           let uu____11982 = FStar_Syntax_Subst.compress t  in
           uu____11982.FStar_Syntax_Syntax.n  in
         match uu____11981 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____11987)) -> s = "uninterpreted_by_smt"
         | uu____11992 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11998 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12004 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12016 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12017 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12018 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12031 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12033 =
             let uu____12035 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12035  in
           if uu____12033
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12064 ->
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
                let uu____12096 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12096 with
                | (formals,uu____12116) ->
                    let arity = FStar_List.length formals  in
                    let uu____12140 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12140 with
                     | (aname,atok,env2) ->
                         let uu____12166 =
                           let uu____12171 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____12171 env2
                            in
                         (match uu____12166 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12183 =
                                  let uu____12184 =
                                    let uu____12196 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____12216  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12196,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12184
                                   in
                                [uu____12183;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____12233 =
                                let aux uu____12279 uu____12280 =
                                  match (uu____12279, uu____12280) with
                                  | ((bv,uu____12324),(env3,acc_sorts,acc))
                                      ->
                                      let uu____12356 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____12356 with
                                       | (xxsym,xx,env4) ->
                                           let uu____12379 =
                                             let uu____12382 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____12382 :: acc_sorts  in
                                           (env4, uu____12379, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____12233 with
                               | (uu____12414,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____12430 =
                                       let uu____12438 =
                                         let uu____12439 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12440 =
                                           let uu____12451 =
                                             let uu____12452 =
                                               let uu____12457 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____12457)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____12452
                                              in
                                           ([[app]], xs_sorts, uu____12451)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12439 uu____12440
                                          in
                                       (uu____12438,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.strcat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12430
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____12472 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____12472
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____12475 =
                                       let uu____12483 =
                                         let uu____12484 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12485 =
                                           let uu____12496 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____12496)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12484 uu____12485
                                          in
                                       (uu____12483,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.strcat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12475
                                      in
                                   (env2,
                                     (FStar_List.append decls
                                        (FStar_List.append a_decls
                                           [a_eq; tok_correspondence]))))))
                 in
              let uu____12511 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____12511 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12537,uu____12538)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____12539 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____12539 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12561,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____12568 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___376_12574  ->
                       match uu___376_12574 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____12577 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____12583 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____12586 -> false))
                in
             Prims.op_Negation uu____12568  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____12596 =
                let uu____12603 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____12603 env fv t quals  in
              match uu____12596 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____12621 =
                      FStar_SMTEncoding_Term.mk_fv
                        (tname, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____12621
                     in
                  let uu____12623 =
                    let uu____12624 =
                      primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                        lid tname tsym
                       in
                    FStar_List.append decls uu____12624  in
                  (uu____12623, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____12630 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____12630 with
            | (uvs,f1) ->
                let env1 =
                  let uu___394_12642 = env  in
                  let uu____12643 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___394_12642.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___394_12642.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___394_12642.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____12643;
                    FStar_SMTEncoding_Env.warn =
                      (uu___394_12642.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.cache =
                      (uu___394_12642.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___394_12642.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___394_12642.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___394_12642.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___394_12642.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___394_12642.FStar_SMTEncoding_Env.encoding_quantifier)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____12645 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____12645 with
                 | (f3,decls) ->
                     let g =
                       let uu____12659 =
                         let uu____12660 =
                           let uu____12668 =
                             let uu____12669 =
                               let uu____12671 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.format1 "Assumption: %s"
                                 uu____12671
                                in
                             FStar_Pervasives_Native.Some uu____12669  in
                           let uu____12675 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                               (Prims.strcat "assumption_" l.FStar_Ident.str)
                              in
                           (f3, uu____12668, uu____12675)  in
                         FStar_SMTEncoding_Util.mkAssume uu____12660  in
                       [uu____12659]  in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____12680) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____12694 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____12716 =
                        let uu____12719 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____12719.FStar_Syntax_Syntax.fv_name  in
                      uu____12716.FStar_Syntax_Syntax.v  in
                    let uu____12720 =
                      let uu____12722 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____12722  in
                    if uu____12720
                    then
                      let val_decl =
                        let uu___395_12754 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___395_12754.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___395_12754.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___395_12754.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____12755 = encode_sigelt' env1 val_decl  in
                      match uu____12755 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____12694 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____12791,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____12793;
                           FStar_Syntax_Syntax.lbtyp = uu____12794;
                           FStar_Syntax_Syntax.lbeff = uu____12795;
                           FStar_Syntax_Syntax.lbdef = uu____12796;
                           FStar_Syntax_Syntax.lbattrs = uu____12797;
                           FStar_Syntax_Syntax.lbpos = uu____12798;_}::[]),uu____12799)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____12818 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____12818 with
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
                  let uu____12856 =
                    let uu____12859 =
                      let uu____12860 =
                        let uu____12868 =
                          let uu____12869 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____12870 =
                            let uu____12881 =
                              let uu____12882 =
                                let uu____12887 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____12887)  in
                              FStar_SMTEncoding_Util.mkEq uu____12882  in
                            ([[b2t_x]], [xx], uu____12881)  in
                          FStar_SMTEncoding_Term.mkForall uu____12869
                            uu____12870
                           in
                        (uu____12868,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____12860  in
                    [uu____12859]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____12856
                   in
                (decls, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____12925,uu____12926) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___377_12936  ->
                   match uu___377_12936 with
                   | FStar_Syntax_Syntax.Discriminator uu____12938 -> true
                   | uu____12940 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____12942,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____12954 =
                      let uu____12956 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____12956.FStar_Ident.idText  in
                    uu____12954 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___378_12963  ->
                      match uu___378_12963 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____12966 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____12969) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_12983  ->
                   match uu___379_12983 with
                   | FStar_Syntax_Syntax.Projector uu____12985 -> true
                   | uu____12991 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____12995 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____12995 with
            | FStar_Pervasives_Native.Some uu____13002 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___396_13004 = se  in
                  let uu____13005 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13005;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___396_13004.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___396_13004.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___396_13004.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13008) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13023) ->
           let uu____13032 = encode_sigelts env ses  in
           (match uu____13032 with
            | (g,env1) ->
                let uu____13049 =
                  FStar_All.pipe_right g
                    (FStar_List.partition
                       (fun uu___380_13072  ->
                          match uu___380_13072 with
                          | FStar_SMTEncoding_Term.Assume
                              {
                                FStar_SMTEncoding_Term.assumption_term =
                                  uu____13074;
                                FStar_SMTEncoding_Term.assumption_caption =
                                  FStar_Pervasives_Native.Some
                                  "inversion axiom";
                                FStar_SMTEncoding_Term.assumption_name =
                                  uu____13075;
                                FStar_SMTEncoding_Term.assumption_fact_ids =
                                  uu____13076;_}
                              -> false
                          | uu____13083 -> true))
                   in
                (match uu____13049 with
                 | (g',inversions) ->
                     let uu____13099 =
                       FStar_All.pipe_right g'
                         (FStar_List.partition
                            (fun uu___381_13120  ->
                               match uu___381_13120 with
                               | FStar_SMTEncoding_Term.DeclFun uu____13122
                                   -> true
                               | uu____13135 -> false))
                        in
                     (match uu____13099 with
                      | (decls,rest) ->
                          ((FStar_List.append decls
                              (FStar_List.append rest inversions)), env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,uu____13152,tps,k,uu____13155,datas) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let is_logical =
             FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___382_13174  ->
                     match uu___382_13174 with
                     | FStar_Syntax_Syntax.Logic  -> true
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____13178 -> false))
              in
           let constructor_or_logic_type_decl c =
             if is_logical
             then
               let uu____13191 = c  in
               match uu____13191 with
               | (name,args,uu____13196,uu____13197,uu____13198) ->
                   let uu____13209 =
                     let uu____13210 =
                       let uu____13222 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____13249  ->
                                 match uu____13249 with
                                 | (uu____13258,sort,uu____13260) -> sort))
                          in
                       (name, uu____13222, FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                        in
                     FStar_SMTEncoding_Term.DeclFun uu____13210  in
                   [uu____13209]
             else
               (let uu____13271 = FStar_Ident.range_of_lid t  in
                FStar_SMTEncoding_Term.constructor_to_decl uu____13271 c)
              in
           let inversion_axioms tapp vars =
             let uu____13289 =
               FStar_All.pipe_right datas
                 (FStar_Util.for_some
                    (fun l  ->
                       let uu____13297 =
                         FStar_TypeChecker_Env.try_lookup_lid
                           env.FStar_SMTEncoding_Env.tcenv l
                          in
                       FStar_All.pipe_right uu____13297 FStar_Option.isNone))
                in
             if uu____13289
             then []
             else
               (let uu____13332 =
                  FStar_SMTEncoding_Env.fresh_fvar "x"
                    FStar_SMTEncoding_Term.Term_sort
                   in
                match uu____13332 with
                | (xxsym,xx) ->
                    let uu____13345 =
                      FStar_All.pipe_right datas
                        (FStar_List.fold_left
                           (fun uu____13384  ->
                              fun l  ->
                                match uu____13384 with
                                | (out,decls) ->
                                    let uu____13404 =
                                      FStar_TypeChecker_Env.lookup_datacon
                                        env.FStar_SMTEncoding_Env.tcenv l
                                       in
                                    (match uu____13404 with
                                     | (uu____13415,data_t) ->
                                         let uu____13417 =
                                           FStar_Syntax_Util.arrow_formals
                                             data_t
                                            in
                                         (match uu____13417 with
                                          | (args,res) ->
                                              let indices =
                                                let uu____13461 =
                                                  let uu____13462 =
                                                    FStar_Syntax_Subst.compress
                                                      res
                                                     in
                                                  uu____13462.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____13461 with
                                                | FStar_Syntax_Syntax.Tm_app
                                                    (uu____13465,indices) ->
                                                    indices
                                                | uu____13491 -> []  in
                                              let env1 =
                                                FStar_All.pipe_right args
                                                  (FStar_List.fold_left
                                                     (fun env1  ->
                                                        fun uu____13521  ->
                                                          match uu____13521
                                                          with
                                                          | (x,uu____13529)
                                                              ->
                                                              let uu____13534
                                                                =
                                                                let uu____13535
                                                                  =
                                                                  let uu____13543
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                  (uu____13543,
                                                                    [xx])
                                                                   in
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  uu____13535
                                                                 in
                                                              FStar_SMTEncoding_Env.push_term_var
                                                                env1 x
                                                                uu____13534)
                                                     env)
                                                 in
                                              let uu____13548 =
                                                FStar_SMTEncoding_EncodeTerm.encode_args
                                                  indices env1
                                                 in
                                              (match uu____13548 with
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
                                                       let uu____13573 =
                                                         FStar_List.map2
                                                           (fun v1  ->
                                                              fun a  ->
                                                                let uu____13581
                                                                  =
                                                                  let uu____13586
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                  (uu____13586,
                                                                    a)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  uu____13581)
                                                           vars indices1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____13573
                                                         FStar_SMTEncoding_Util.mk_and_l
                                                        in
                                                     let uu____13589 =
                                                       let uu____13590 =
                                                         let uu____13595 =
                                                           let uu____13596 =
                                                             let uu____13601
                                                               =
                                                               FStar_SMTEncoding_Env.mk_data_tester
                                                                 env1 l xx
                                                                in
                                                             (uu____13601,
                                                               eqs)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____13596
                                                            in
                                                         (out, uu____13595)
                                                          in
                                                       FStar_SMTEncoding_Util.mkOr
                                                         uu____13590
                                                        in
                                                     (uu____13589,
                                                       (FStar_List.append
                                                          decls decls'))))))))
                           (FStar_SMTEncoding_Util.mkFalse, []))
                       in
                    (match uu____13345 with
                     | (data_ax,decls) ->
                         let uu____13614 =
                           FStar_SMTEncoding_Env.fresh_fvar "f"
                             FStar_SMTEncoding_Term.Fuel_sort
                            in
                         (match uu____13614 with
                          | (ffsym,ff) ->
                              let fuel_guarded_inversion =
                                let xx_has_type_sfuel =
                                  if
                                    (FStar_List.length datas) >
                                      (Prims.parse_int "1")
                                  then
                                    let uu____13631 =
                                      FStar_SMTEncoding_Util.mkApp
                                        ("SFuel", [ff])
                                       in
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel
                                      uu____13631 xx tapp
                                  else
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                      xx tapp
                                   in
                                let uu____13638 =
                                  let uu____13646 =
                                    let uu____13647 =
                                      FStar_Ident.range_of_lid t  in
                                    let uu____13648 =
                                      let uu____13659 =
                                        let uu____13660 =
                                          FStar_SMTEncoding_Term.mk_fv
                                            (ffsym,
                                              FStar_SMTEncoding_Term.Fuel_sort)
                                           in
                                        let uu____13662 =
                                          let uu____13665 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             in
                                          uu____13665 :: vars  in
                                        FStar_SMTEncoding_Env.add_fuel
                                          uu____13660 uu____13662
                                         in
                                      let uu____13667 =
                                        FStar_SMTEncoding_Util.mkImp
                                          (xx_has_type_sfuel, data_ax)
                                         in
                                      ([[xx_has_type_sfuel]], uu____13659,
                                        uu____13667)
                                       in
                                    FStar_SMTEncoding_Term.mkForall
                                      uu____13647 uu____13648
                                     in
                                  let uu____13676 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                      (Prims.strcat "fuel_guarded_inversion_"
                                         t.FStar_Ident.str)
                                     in
                                  (uu____13646,
                                    (FStar_Pervasives_Native.Some
                                       "inversion axiom"), uu____13676)
                                   in
                                FStar_SMTEncoding_Util.mkAssume uu____13638
                                 in
                              FStar_List.append decls
                                [fuel_guarded_inversion])))
              in
           let uu____13682 =
             let uu____13687 =
               let uu____13688 = FStar_Syntax_Subst.compress k  in
               uu____13688.FStar_Syntax_Syntax.n  in
             match uu____13687 with
             | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                 ((FStar_List.append tps formals),
                   (FStar_Syntax_Util.comp_result kres))
             | uu____13723 -> (tps, k)  in
           (match uu____13682 with
            | (formals,res) ->
                let uu____13730 = FStar_Syntax_Subst.open_term formals res
                   in
                (match uu____13730 with
                 | (formals1,res1) ->
                     let uu____13741 =
                       FStar_SMTEncoding_EncodeTerm.encode_binders
                         FStar_Pervasives_Native.None formals1 env
                        in
                     (match uu____13741 with
                      | (vars,guards,env',binder_decls,uu____13766) ->
                          let arity = FStar_List.length vars  in
                          let uu____13780 =
                            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                              env t arity
                             in
                          (match uu____13780 with
                           | (tname,ttok,env1) ->
                               let ttok_tm =
                                 FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                               let guard =
                                 FStar_SMTEncoding_Util.mk_and_l guards  in
                               let tapp =
                                 let uu____13810 =
                                   let uu____13818 =
                                     FStar_List.map
                                       FStar_SMTEncoding_Util.mkFreeV vars
                                      in
                                   (tname, uu____13818)  in
                                 FStar_SMTEncoding_Util.mkApp uu____13810  in
                               let uu____13824 =
                                 let tname_decl =
                                   let uu____13834 =
                                     let uu____13835 =
                                       FStar_All.pipe_right vars
                                         (FStar_List.map
                                            (fun fv  ->
                                               let uu____13854 =
                                                 let uu____13856 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     fv
                                                    in
                                                 Prims.strcat tname
                                                   uu____13856
                                                  in
                                               let uu____13858 =
                                                 FStar_SMTEncoding_Term.fv_sort
                                                   fv
                                                  in
                                               (uu____13854, uu____13858,
                                                 false)))
                                        in
                                     let uu____13862 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     (tname, uu____13835,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       uu____13862, false)
                                      in
                                   constructor_or_logic_type_decl uu____13834
                                    in
                                 let uu____13870 =
                                   match vars with
                                   | [] ->
                                       let uu____13883 =
                                         let uu____13884 =
                                           let uu____13887 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (tname, [])
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_3  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_3) uu____13887
                                            in
                                         FStar_SMTEncoding_Env.push_free_var
                                           env1 t arity tname uu____13884
                                          in
                                       ([], uu____13883)
                                   | uu____13899 ->
                                       let ttok_decl =
                                         FStar_SMTEncoding_Term.DeclFun
                                           (ttok, [],
                                             FStar_SMTEncoding_Term.Term_sort,
                                             (FStar_Pervasives_Native.Some
                                                "token"))
                                          in
                                       let ttok_fresh =
                                         let uu____13909 =
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                             ()
                                            in
                                         FStar_SMTEncoding_Term.fresh_token
                                           (ttok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                           uu____13909
                                          in
                                       let ttok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           ttok_tm vars
                                          in
                                       let pats = [[ttok_app]; [tapp]]  in
                                       let name_tok_corr =
                                         let uu____13925 =
                                           let uu____13933 =
                                             let uu____13934 =
                                               FStar_Ident.range_of_lid t  in
                                             let uu____13935 =
                                               let uu____13951 =
                                                 FStar_SMTEncoding_Util.mkEq
                                                   (ttok_app, tapp)
                                                  in
                                               (pats,
                                                 FStar_Pervasives_Native.None,
                                                 vars, uu____13951)
                                                in
                                             FStar_SMTEncoding_Term.mkForall'
                                               uu____13934 uu____13935
                                              in
                                           (uu____13933,
                                             (FStar_Pervasives_Native.Some
                                                "name-token correspondence"),
                                             (Prims.strcat
                                                "token_correspondence_" ttok))
                                            in
                                         FStar_SMTEncoding_Util.mkAssume
                                           uu____13925
                                          in
                                       ([ttok_decl;
                                        ttok_fresh;
                                        name_tok_corr], env1)
                                    in
                                 match uu____13870 with
                                 | (tok_decls,env2) ->
                                     let uu____13978 =
                                       FStar_Ident.lid_equals t
                                         FStar_Parser_Const.lex_t_lid
                                        in
                                     if uu____13978
                                     then (tok_decls, env2)
                                     else
                                       ((FStar_List.append tname_decl
                                           tok_decls), env2)
                                  in
                               (match uu____13824 with
                                | (decls,env2) ->
                                    let kindingAx =
                                      let uu____14006 =
                                        FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                          FStar_Pervasives_Native.None res1
                                          env' tapp
                                         in
                                      match uu____14006 with
                                      | (k1,decls1) ->
                                          let karr =
                                            if
                                              (FStar_List.length formals1) >
                                                (Prims.parse_int "0")
                                            then
                                              let uu____14028 =
                                                let uu____14029 =
                                                  let uu____14037 =
                                                    let uu____14038 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        ttok_tm
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____14038
                                                     in
                                                  (uu____14037,
                                                    (FStar_Pervasives_Native.Some
                                                       "kinding"),
                                                    (Prims.strcat
                                                       "pre_kinding_" ttok))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____14029
                                                 in
                                              [uu____14028]
                                            else []  in
                                          let uu____14046 =
                                            let uu____14049 =
                                              let uu____14052 =
                                                let uu____14053 =
                                                  let uu____14061 =
                                                    let uu____14062 =
                                                      FStar_Ident.range_of_lid
                                                        t
                                                       in
                                                    let uu____14063 =
                                                      let uu____14074 =
                                                        FStar_SMTEncoding_Util.mkImp
                                                          (guard, k1)
                                                         in
                                                      ([[tapp]], vars,
                                                        uu____14074)
                                                       in
                                                    FStar_SMTEncoding_Term.mkForall
                                                      uu____14062 uu____14063
                                                     in
                                                  (uu____14061,
                                                    FStar_Pervasives_Native.None,
                                                    (Prims.strcat "kinding_"
                                                       ttok))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____14053
                                                 in
                                              [uu____14052]  in
                                            FStar_List.append karr
                                              uu____14049
                                             in
                                          FStar_List.append decls1
                                            uu____14046
                                       in
                                    let aux =
                                      let uu____14089 =
                                        let uu____14092 =
                                          inversion_axioms tapp vars  in
                                        let uu____14095 =
                                          let uu____14098 =
                                            let uu____14099 =
                                              FStar_Ident.range_of_lid t  in
                                            pretype_axiom uu____14099 env2
                                              tapp vars
                                             in
                                          [uu____14098]  in
                                        FStar_List.append uu____14092
                                          uu____14095
                                         in
                                      FStar_List.append kindingAx uu____14089
                                       in
                                    let g =
                                      FStar_List.append decls
                                        (FStar_List.append binder_decls aux)
                                       in
                                    (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____14104,uu____14105,uu____14106,uu____14107,uu____14108)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____14116,t,uu____14118,n_tps,uu____14120) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____14130 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____14130 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____14178 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____14178 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____14206 =
                       FStar_SMTEncoding_Env.fresh_fvar "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____14206 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____14226 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____14226 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____14305 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____14305,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____14312 =
                                   let uu____14313 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____14313, true)
                                    in
                                 let uu____14321 =
                                   let uu____14328 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____14328
                                    in
                                 FStar_All.pipe_right uu____14312 uu____14321
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
                               let uu____14340 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____14340 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____14352::uu____14353 ->
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
                                            let uu____14402 =
                                              let uu____14403 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____14403]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____14402
                                             in
                                          let uu____14429 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____14430 =
                                            let uu____14441 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____14441)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____14429 uu____14430
                                      | uu____14468 -> tok_typing  in
                                    let uu____14479 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____14479 with
                                     | (vars',guards',env'',decls_formals,uu____14504)
                                         ->
                                         let uu____14517 =
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
                                         (match uu____14517 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____14547 ->
                                                    let uu____14556 =
                                                      let uu____14557 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____14557
                                                       in
                                                    [uu____14556]
                                                 in
                                              let encode_elim uu____14573 =
                                                let uu____14574 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____14574 with
                                                | (head1,args) ->
                                                    let uu____14625 =
                                                      let uu____14626 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____14626.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____14625 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____14638;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____14639;_},uu____14640)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____14646 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____14646
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
                                                                  | uu____14709
                                                                    ->
                                                                    let uu____14710
                                                                    =
                                                                    let uu____14716
                                                                    =
                                                                    let uu____14718
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14718
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14716)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14710
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14741
                                                                    =
                                                                    let uu____14743
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14743
                                                                     in
                                                                    if
                                                                    uu____14741
                                                                    then
                                                                    let uu____14765
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14765]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____14768
                                                                =
                                                                let uu____14782
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____14839
                                                                     ->
                                                                    fun
                                                                    uu____14840
                                                                     ->
                                                                    match 
                                                                    (uu____14839,
                                                                    uu____14840)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14951
                                                                    =
                                                                    let uu____14959
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14959
                                                                     in
                                                                    (match uu____14951
                                                                    with
                                                                    | 
                                                                    (uu____14973,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14984
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14984
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14989
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14989
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
                                                                  uu____14782
                                                                 in
                                                              (match uu____14768
                                                               with
                                                               | (uu____15010,arg_vars,elim_eqns_or_guards,uu____15013)
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
                                                                    let uu____15040
                                                                    =
                                                                    let uu____15048
                                                                    =
                                                                    let uu____15049
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15050
                                                                    =
                                                                    let uu____15061
                                                                    =
                                                                    let uu____15062
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15062
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15064
                                                                    =
                                                                    let uu____15065
                                                                    =
                                                                    let uu____15070
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15070)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15065
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15061,
                                                                    uu____15064)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15049
                                                                    uu____15050
                                                                     in
                                                                    (uu____15048,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15040
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15085
                                                                    =
                                                                    let uu____15086
                                                                    =
                                                                    let uu____15092
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15092,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____15086
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15085
                                                                     in
                                                                    let uu____15095
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15095
                                                                    then
                                                                    let x =
                                                                    let uu____15099
                                                                    =
                                                                    let uu____15105
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15105,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____15099
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15110
                                                                    =
                                                                    let uu____15118
                                                                    =
                                                                    let uu____15119
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15120
                                                                    =
                                                                    let uu____15131
                                                                    =
                                                                    let uu____15136
                                                                    =
                                                                    let uu____15139
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15139]
                                                                     in
                                                                    [uu____15136]
                                                                     in
                                                                    let uu____15144
                                                                    =
                                                                    let uu____15145
                                                                    =
                                                                    let uu____15150
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15152
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15150,
                                                                    uu____15152)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15145
                                                                     in
                                                                    (uu____15131,
                                                                    [x],
                                                                    uu____15144)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15119
                                                                    uu____15120
                                                                     in
                                                                    let uu____15173
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15118,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15173)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15110
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15184
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
                                                                    (let uu____15207
                                                                    =
                                                                    let uu____15208
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15208
                                                                    dapp1  in
                                                                    [uu____15207])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15184
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15215
                                                                    =
                                                                    let uu____15223
                                                                    =
                                                                    let uu____15224
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15225
                                                                    =
                                                                    let uu____15236
                                                                    =
                                                                    let uu____15237
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15237
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15239
                                                                    =
                                                                    let uu____15240
                                                                    =
                                                                    let uu____15245
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15245)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15240
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15236,
                                                                    uu____15239)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15224
                                                                    uu____15225
                                                                     in
                                                                    (uu____15223,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15215)
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
                                                         let uu____15264 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____15264
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
                                                                  | uu____15327
                                                                    ->
                                                                    let uu____15328
                                                                    =
                                                                    let uu____15334
                                                                    =
                                                                    let uu____15336
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15336
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15334)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15328
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15359
                                                                    =
                                                                    let uu____15361
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15361
                                                                     in
                                                                    if
                                                                    uu____15359
                                                                    then
                                                                    let uu____15383
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15383]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____15386
                                                                =
                                                                let uu____15400
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____15457
                                                                     ->
                                                                    fun
                                                                    uu____15458
                                                                     ->
                                                                    match 
                                                                    (uu____15457,
                                                                    uu____15458)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15569
                                                                    =
                                                                    let uu____15577
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15577
                                                                     in
                                                                    (match uu____15569
                                                                    with
                                                                    | 
                                                                    (uu____15591,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15602
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15602
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15607
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15607
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
                                                                  uu____15400
                                                                 in
                                                              (match uu____15386
                                                               with
                                                               | (uu____15628,arg_vars,elim_eqns_or_guards,uu____15631)
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
                                                                    let uu____15658
                                                                    =
                                                                    let uu____15666
                                                                    =
                                                                    let uu____15667
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15668
                                                                    =
                                                                    let uu____15679
                                                                    =
                                                                    let uu____15680
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15680
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15682
                                                                    =
                                                                    let uu____15683
                                                                    =
                                                                    let uu____15688
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15688)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15683
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15679,
                                                                    uu____15682)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15667
                                                                    uu____15668
                                                                     in
                                                                    (uu____15666,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15658
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15703
                                                                    =
                                                                    let uu____15704
                                                                    =
                                                                    let uu____15710
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15710,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____15704
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15703
                                                                     in
                                                                    let uu____15713
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15713
                                                                    then
                                                                    let x =
                                                                    let uu____15717
                                                                    =
                                                                    let uu____15723
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15723,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____15717
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15728
                                                                    =
                                                                    let uu____15736
                                                                    =
                                                                    let uu____15737
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15738
                                                                    =
                                                                    let uu____15749
                                                                    =
                                                                    let uu____15754
                                                                    =
                                                                    let uu____15757
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15757]
                                                                     in
                                                                    [uu____15754]
                                                                     in
                                                                    let uu____15762
                                                                    =
                                                                    let uu____15763
                                                                    =
                                                                    let uu____15768
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15770
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15768,
                                                                    uu____15770)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15763
                                                                     in
                                                                    (uu____15749,
                                                                    [x],
                                                                    uu____15762)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15737
                                                                    uu____15738
                                                                     in
                                                                    let uu____15791
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15736,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15791)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15728
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15802
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
                                                                    (let uu____15825
                                                                    =
                                                                    let uu____15826
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15826
                                                                    dapp1  in
                                                                    [uu____15825])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15802
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15833
                                                                    =
                                                                    let uu____15841
                                                                    =
                                                                    let uu____15842
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15843
                                                                    =
                                                                    let uu____15854
                                                                    =
                                                                    let uu____15855
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15855
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15857
                                                                    =
                                                                    let uu____15858
                                                                    =
                                                                    let uu____15863
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15863)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15858
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15854,
                                                                    uu____15857)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15842
                                                                    uu____15843
                                                                     in
                                                                    (uu____15841,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15833)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____15880 ->
                                                         ((let uu____15882 =
                                                             let uu____15888
                                                               =
                                                               let uu____15890
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____15892
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____15890
                                                                 uu____15892
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____15888)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____15882);
                                                          ([], [])))
                                                 in
                                              let uu____15900 =
                                                encode_elim ()  in
                                              (match uu____15900 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____15926 =
                                                       let uu____15929 =
                                                         let uu____15932 =
                                                           let uu____15935 =
                                                             let uu____15938
                                                               =
                                                               let uu____15939
                                                                 =
                                                                 let uu____15951
                                                                   =
                                                                   let uu____15952
                                                                    =
                                                                    let uu____15954
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15954
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____15952
                                                                    in
                                                                 (ddtok, [],
                                                                   FStar_SMTEncoding_Term.Term_sort,
                                                                   uu____15951)
                                                                  in
                                                               FStar_SMTEncoding_Term.DeclFun
                                                                 uu____15939
                                                                in
                                                             [uu____15938]
                                                              in
                                                           let uu____15961 =
                                                             let uu____15964
                                                               =
                                                               let uu____15967
                                                                 =
                                                                 let uu____15970
                                                                   =
                                                                   let uu____15973
                                                                    =
                                                                    let uu____15976
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____15981
                                                                    =
                                                                    let uu____15984
                                                                    =
                                                                    let uu____15985
                                                                    =
                                                                    let uu____15993
                                                                    =
                                                                    let uu____15994
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15995
                                                                    =
                                                                    let uu____16006
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16006)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15994
                                                                    uu____15995
                                                                     in
                                                                    (uu____15993,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15985
                                                                     in
                                                                    let uu____16019
                                                                    =
                                                                    let uu____16022
                                                                    =
                                                                    let uu____16023
                                                                    =
                                                                    let uu____16031
                                                                    =
                                                                    let uu____16032
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16033
                                                                    =
                                                                    let uu____16044
                                                                    =
                                                                    let uu____16045
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16045
                                                                    vars'  in
                                                                    let uu____16047
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____16044,
                                                                    uu____16047)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16032
                                                                    uu____16033
                                                                     in
                                                                    (uu____16031,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16023
                                                                     in
                                                                    [uu____16022]
                                                                     in
                                                                    uu____15984
                                                                    ::
                                                                    uu____16019
                                                                     in
                                                                    uu____15976
                                                                    ::
                                                                    uu____15981
                                                                     in
                                                                   FStar_List.append
                                                                    uu____15973
                                                                    elim
                                                                    in
                                                                 FStar_List.append
                                                                   decls_pred
                                                                   uu____15970
                                                                  in
                                                               FStar_List.append
                                                                 decls_formals
                                                                 uu____15967
                                                                in
                                                             FStar_List.append
                                                               proxy_fresh
                                                               uu____15964
                                                              in
                                                           FStar_List.append
                                                             uu____15935
                                                             uu____15961
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____15932
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____15929
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____15926
                                                      in
                                                   ((FStar_List.append
                                                       datacons g), env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____16085  ->
              fun se  ->
                match uu____16085 with
                | (g,env1) ->
                    let uu____16105 = encode_sigelt env1 se  in
                    (match uu____16105 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16173 =
        match uu____16173 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____16210 ->
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
                 ((let uu____16218 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____16218
                   then
                     let uu____16223 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____16225 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____16227 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16223 uu____16225 uu____16227
                   else ());
                  (let uu____16232 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____16232 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____16250 =
                         let uu____16258 =
                           let uu____16260 =
                             let uu____16262 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____16262
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____16260  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____16258
                          in
                       (match uu____16250 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____16282 = FStar_Options.log_queries ()
                                 in
                              if uu____16282
                              then
                                let uu____16285 =
                                  let uu____16287 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____16289 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____16291 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16287 uu____16289 uu____16291
                                   in
                                FStar_Pervasives_Native.Some uu____16285
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____16315,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____16335 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____16335 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____16362 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____16362 with | (uu____16389,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____16442  ->
              match uu____16442 with
              | (l,uu____16451,uu____16452) ->
                  let uu____16455 =
                    let uu____16467 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____16467, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____16455))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____16500  ->
              match uu____16500 with
              | (l,uu____16511,uu____16512) ->
                  let uu____16515 =
                    let uu____16516 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      uu____16516
                     in
                  let uu____16519 =
                    let uu____16522 =
                      let uu____16523 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____16523  in
                    [uu____16522]  in
                  uu____16515 :: uu____16519))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____16552 =
      let uu____16555 =
        let uu____16556 = FStar_Util.psmap_empty ()  in
        let uu____16571 = FStar_Util.psmap_empty ()  in
        let uu____16574 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____16578 =
          let uu____16580 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____16580 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____16556;
          FStar_SMTEncoding_Env.fvar_bindings = uu____16571;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____16574;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____16578;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____16555]  in
    FStar_ST.op_Colon_Equals last_env uu____16552
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____16622 = FStar_ST.op_Bang last_env  in
      match uu____16622 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16650 ->
          let uu___397_16653 = e  in
          let uu____16654 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___397_16653.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___397_16653.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___397_16653.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___397_16653.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___397_16653.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___397_16653.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___397_16653.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___397_16653.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____16654;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___397_16653.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____16662 = FStar_ST.op_Bang last_env  in
    match uu____16662 with
    | [] -> failwith "Empty env stack"
    | uu____16689::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____16721  ->
    let uu____16722 = FStar_ST.op_Bang last_env  in
    match uu____16722 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____16782  ->
    let uu____16783 = FStar_ST.op_Bang last_env  in
    match uu____16783 with
    | [] -> failwith "Popping an empty stack"
    | uu____16810::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____16847  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____16900  ->
         let uu____16901 = snapshot_env ()  in
         match uu____16901 with
         | (env_depth,()) ->
             let uu____16923 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____16923 with
              | (varops_depth,()) ->
                  let uu____16945 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____16945 with
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
        (fun uu____17003  ->
           let uu____17004 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____17004 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____17099 = snapshot msg  in () 
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
        | (uu____17145::uu____17146,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___398_17154 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___398_17154.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___398_17154.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___398_17154.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____17155 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____17175 =
        let uu____17178 =
          let uu____17179 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____17179  in
        let uu____17180 = open_fact_db_tags env  in uu____17178 ::
          uu____17180
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____17175
  
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____17207 = encode_sigelt env se  in
      match uu____17207 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____17252 = FStar_Options.log_queries ()  in
        if uu____17252
        then
          let uu____17257 =
            let uu____17258 =
              let uu____17260 =
                let uu____17262 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____17262 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____17260  in
            FStar_SMTEncoding_Term.Caption uu____17258  in
          uu____17257 :: decls
        else decls  in
      (let uu____17281 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____17281
       then
         let uu____17284 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____17284
       else ());
      (let env =
         let uu____17290 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____17290 tcenv  in
       let uu____17291 = encode_top_level_facts env se  in
       match uu____17291 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____17305 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____17305)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____17319 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____17319
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____17334 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
          if uu____17334
          then
            let uu____17337 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____17337
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____17383  ->
                    fun se  ->
                      match uu____17383 with
                      | (g,env2) ->
                          let uu____17403 = encode_top_level_facts env2 se
                             in
                          (match uu____17403 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____17426 =
            encode_signature
              (let uu___399_17435 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___399_17435.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___399_17435.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___399_17435.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___399_17435.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___399_17435.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___399_17435.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___399_17435.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___399_17435.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___399_17435.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___399_17435.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____17426 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____17455 = FStar_Options.log_queries ()  in
                if uu____17455
                then
                  let msg = Prims.strcat "Externals for " name  in
                  [FStar_SMTEncoding_Term.Module
                     (name,
                       (FStar_List.append
                          ((FStar_SMTEncoding_Term.Caption msg) :: decls1)
                          [FStar_SMTEncoding_Term.Caption
                             (Prims.strcat "End " msg)]))]
                else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
              (set_env
                 (let uu___400_17475 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___400_17475.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___400_17475.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___400_17475.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___400_17475.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___400_17475.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___400_17475.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___400_17475.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___400_17475.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___400_17475.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___400_17475.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____17478 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____17478
                then
                  FStar_Util.print1 "Done encoding externals for %s\n" name
                else ());
               (let decls1 = caption decls  in
                FStar_SMTEncoding_Z3.giveZ3 decls1))))
  
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
        (let uu____17543 =
           let uu____17545 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____17545.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17543);
        (let env =
           let uu____17547 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____17547 tcenv  in
         let uu____17548 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____17587 = aux rest  in
                 (match uu____17587 with
                  | (out,rest1) ->
                      let t =
                        let uu____17615 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____17615 with
                        | FStar_Pervasives_Native.Some uu____17618 ->
                            let uu____17619 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____17619
                              x.FStar_Syntax_Syntax.sort
                        | uu____17620 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____17624 =
                        let uu____17627 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___401_17630 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___401_17630.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___401_17630.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____17627 :: out  in
                      (uu____17624, rest1))
             | uu____17635 -> ([], bindings)  in
           let uu____17642 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____17642 with
           | (closing,bindings) ->
               let uu____17669 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____17669, bindings)
            in
         match uu____17548 with
         | (q1,bindings) ->
             let uu____17700 = encode_env_bindings env bindings  in
             (match uu____17700 with
              | (env_decls,env1) ->
                  ((let uu____17722 =
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
                    if uu____17722
                    then
                      let uu____17729 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17729
                    else ());
                   (let uu____17734 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____17734 with
                    | (phi,qdecls) ->
                        let uu____17755 =
                          let uu____17760 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17760 phi
                           in
                        (match uu____17755 with
                         | (labels,phi1) ->
                             let uu____17777 = encode_labels labels  in
                             (match uu____17777 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17813 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17813
                                    then
                                      let uu____17818 =
                                        let uu____17819 =
                                          let uu____17821 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17821
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17819
                                         in
                                      [uu____17818]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____17830 =
                                      let uu____17838 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____17839 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____17838,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17839)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17830
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
  