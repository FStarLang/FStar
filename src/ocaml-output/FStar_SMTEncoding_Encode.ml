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
  let uu____140 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____140 with
  | (asym,a) ->
      let uu____151 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____151 with
       | (xsym,x) ->
           let uu____162 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____162 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____240 =
                      let uu____252 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____252, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____240  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____272 =
                      let uu____280 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____280)  in
                    FStar_SMTEncoding_Util.mkApp uu____272  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____299 =
                    let uu____302 =
                      let uu____305 =
                        let uu____308 =
                          let uu____309 =
                            let uu____317 =
                              let uu____318 =
                                let uu____329 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____329)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____318
                               in
                            (uu____317, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____309  in
                        let uu____341 =
                          let uu____344 =
                            let uu____345 =
                              let uu____353 =
                                let uu____354 =
                                  let uu____365 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____365)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____354
                                 in
                              (uu____353,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____345  in
                          [uu____344]  in
                        uu____308 :: uu____341  in
                      xtok_decl :: uu____305  in
                    xname_decl :: uu____302  in
                  (xtok1, (FStar_List.length vars), uu____299)  in
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
                  let uu____535 =
                    let uu____556 =
                      let uu____575 =
                        let uu____576 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____576
                         in
                      quant axy uu____575  in
                    (FStar_Parser_Const.op_Eq, uu____556)  in
                  let uu____593 =
                    let uu____616 =
                      let uu____637 =
                        let uu____656 =
                          let uu____657 =
                            let uu____658 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____658  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____657
                           in
                        quant axy uu____656  in
                      (FStar_Parser_Const.op_notEq, uu____637)  in
                    let uu____675 =
                      let uu____698 =
                        let uu____719 =
                          let uu____738 =
                            let uu____739 =
                              let uu____740 =
                                let uu____745 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____746 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____745, uu____746)  in
                              FStar_SMTEncoding_Util.mkAnd uu____740  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____739
                             in
                          quant xy uu____738  in
                        (FStar_Parser_Const.op_And, uu____719)  in
                      let uu____763 =
                        let uu____786 =
                          let uu____807 =
                            let uu____826 =
                              let uu____827 =
                                let uu____828 =
                                  let uu____833 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____834 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____833, uu____834)  in
                                FStar_SMTEncoding_Util.mkOr uu____828  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____827
                               in
                            quant xy uu____826  in
                          (FStar_Parser_Const.op_Or, uu____807)  in
                        let uu____851 =
                          let uu____874 =
                            let uu____895 =
                              let uu____914 =
                                let uu____915 =
                                  let uu____916 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____916  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____915
                                 in
                              quant qx uu____914  in
                            (FStar_Parser_Const.op_Negation, uu____895)  in
                          let uu____933 =
                            let uu____956 =
                              let uu____977 =
                                let uu____996 =
                                  let uu____997 =
                                    let uu____998 =
                                      let uu____1003 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1004 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1003, uu____1004)  in
                                    FStar_SMTEncoding_Util.mkLT uu____998  in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____997
                                   in
                                quant xy uu____996  in
                              (FStar_Parser_Const.op_LT, uu____977)  in
                            let uu____1021 =
                              let uu____1044 =
                                let uu____1065 =
                                  let uu____1084 =
                                    let uu____1085 =
                                      let uu____1086 =
                                        let uu____1091 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1092 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1091, uu____1092)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1086
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1085
                                     in
                                  quant xy uu____1084  in
                                (FStar_Parser_Const.op_LTE, uu____1065)  in
                              let uu____1109 =
                                let uu____1132 =
                                  let uu____1153 =
                                    let uu____1172 =
                                      let uu____1173 =
                                        let uu____1174 =
                                          let uu____1179 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1180 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1179, uu____1180)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1174
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1173
                                       in
                                    quant xy uu____1172  in
                                  (FStar_Parser_Const.op_GT, uu____1153)  in
                                let uu____1197 =
                                  let uu____1220 =
                                    let uu____1241 =
                                      let uu____1260 =
                                        let uu____1261 =
                                          let uu____1262 =
                                            let uu____1267 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1268 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1267, uu____1268)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1262
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1261
                                         in
                                      quant xy uu____1260  in
                                    (FStar_Parser_Const.op_GTE, uu____1241)
                                     in
                                  let uu____1285 =
                                    let uu____1308 =
                                      let uu____1329 =
                                        let uu____1348 =
                                          let uu____1349 =
                                            let uu____1350 =
                                              let uu____1355 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1356 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1355, uu____1356)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1350
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1349
                                           in
                                        quant xy uu____1348  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1329)
                                       in
                                    let uu____1373 =
                                      let uu____1396 =
                                        let uu____1417 =
                                          let uu____1436 =
                                            let uu____1437 =
                                              let uu____1438 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1438
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1437
                                             in
                                          quant qx uu____1436  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1417)
                                         in
                                      let uu____1455 =
                                        let uu____1478 =
                                          let uu____1499 =
                                            let uu____1518 =
                                              let uu____1519 =
                                                let uu____1520 =
                                                  let uu____1525 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1526 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1525, uu____1526)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1520
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1519
                                               in
                                            quant xy uu____1518  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1499)
                                           in
                                        let uu____1543 =
                                          let uu____1566 =
                                            let uu____1587 =
                                              let uu____1606 =
                                                let uu____1607 =
                                                  let uu____1608 =
                                                    let uu____1613 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____1614 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____1613, uu____1614)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____1608
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____1607
                                                 in
                                              quant xy uu____1606  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____1587)
                                             in
                                          let uu____1631 =
                                            let uu____1654 =
                                              let uu____1675 =
                                                let uu____1694 =
                                                  let uu____1695 =
                                                    let uu____1696 =
                                                      let uu____1701 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____1702 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____1701,
                                                        uu____1702)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____1696
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____1695
                                                   in
                                                quant xy uu____1694  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____1675)
                                               in
                                            let uu____1719 =
                                              let uu____1742 =
                                                let uu____1763 =
                                                  let uu____1782 =
                                                    let uu____1783 =
                                                      let uu____1784 =
                                                        let uu____1789 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____1790 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____1789,
                                                          uu____1790)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____1784
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____1783
                                                     in
                                                  quant xy uu____1782  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____1763)
                                                 in
                                              let uu____1807 =
                                                let uu____1830 =
                                                  let uu____1851 =
                                                    let uu____1870 =
                                                      let uu____1871 =
                                                        let uu____1872 =
                                                          let uu____1877 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____1878 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____1877,
                                                            uu____1878)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____1872
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____1871
                                                       in
                                                    quant xy uu____1870  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____1851)
                                                   in
                                                let uu____1895 =
                                                  let uu____1918 =
                                                    let uu____1939 =
                                                      let uu____1958 =
                                                        let uu____1959 =
                                                          let uu____1960 =
                                                            let uu____1965 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____1966 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____1965,
                                                              uu____1966)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____1960
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____1959
                                                         in
                                                      quant xy uu____1958  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____1939)
                                                     in
                                                  let uu____1983 =
                                                    let uu____2006 =
                                                      let uu____2027 =
                                                        let uu____2046 =
                                                          let uu____2047 =
                                                            let uu____2048 =
                                                              let uu____2053
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2054
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2053,
                                                                uu____2054)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2048
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2047
                                                           in
                                                        quant xy uu____2046
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2027)
                                                       in
                                                    let uu____2071 =
                                                      let uu____2094 =
                                                        let uu____2115 =
                                                          let uu____2134 =
                                                            let uu____2135 =
                                                              let uu____2136
                                                                =
                                                                let uu____2141
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2142
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2141,
                                                                  uu____2142)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2136
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2135
                                                             in
                                                          quant xy uu____2134
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2115)
                                                         in
                                                      let uu____2159 =
                                                        let uu____2182 =
                                                          let uu____2203 =
                                                            let uu____2222 =
                                                              let uu____2223
                                                                =
                                                                let uu____2224
                                                                  =
                                                                  let uu____2229
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2230
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2229,
                                                                    uu____2230)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2224
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2223
                                                               in
                                                            quant xy
                                                              uu____2222
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2203)
                                                           in
                                                        let uu____2247 =
                                                          let uu____2270 =
                                                            let uu____2291 =
                                                              let uu____2310
                                                                =
                                                                let uu____2311
                                                                  =
                                                                  let uu____2312
                                                                    =
                                                                    let uu____2317
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2318
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2317,
                                                                    uu____2318)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2312
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2311
                                                                 in
                                                              quant xy
                                                                uu____2310
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2291)
                                                             in
                                                          let uu____2335 =
                                                            let uu____2358 =
                                                              let uu____2379
                                                                =
                                                                let uu____2398
                                                                  =
                                                                  let uu____2399
                                                                    =
                                                                    let uu____2400
                                                                    =
                                                                    let uu____2405
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2406
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2405,
                                                                    uu____2406)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2400
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2399
                                                                   in
                                                                quant xy
                                                                  uu____2398
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2379)
                                                               in
                                                            let uu____2423 =
                                                              let uu____2446
                                                                =
                                                                let uu____2467
                                                                  =
                                                                  let uu____2486
                                                                    =
                                                                    let uu____2487
                                                                    =
                                                                    let uu____2488
                                                                    =
                                                                    let uu____2493
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2494
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2493,
                                                                    uu____2494)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2488
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2487
                                                                     in
                                                                  quant xy
                                                                    uu____2486
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2467)
                                                                 in
                                                              let uu____2511
                                                                =
                                                                let uu____2534
                                                                  =
                                                                  let uu____2555
                                                                    =
                                                                    let uu____2574
                                                                    =
                                                                    let uu____2575
                                                                    =
                                                                    let uu____2576
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____2576
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2575
                                                                     in
                                                                    quant qx
                                                                    uu____2574
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____2555)
                                                                   in
                                                                [uu____2534]
                                                                 in
                                                              uu____2446 ::
                                                                uu____2511
                                                               in
                                                            uu____2358 ::
                                                              uu____2423
                                                             in
                                                          uu____2270 ::
                                                            uu____2335
                                                           in
                                                        uu____2182 ::
                                                          uu____2247
                                                         in
                                                      uu____2094 ::
                                                        uu____2159
                                                       in
                                                    uu____2006 :: uu____2071
                                                     in
                                                  uu____1918 :: uu____1983
                                                   in
                                                uu____1830 :: uu____1895  in
                                              uu____1742 :: uu____1807  in
                                            uu____1654 :: uu____1719  in
                                          uu____1566 :: uu____1631  in
                                        uu____1478 :: uu____1543  in
                                      uu____1396 :: uu____1455  in
                                    uu____1308 :: uu____1373  in
                                  uu____1220 :: uu____1285  in
                                uu____1132 :: uu____1197  in
                              uu____1044 :: uu____1109  in
                            uu____956 :: uu____1021  in
                          uu____874 :: uu____933  in
                        uu____786 :: uu____851  in
                      uu____698 :: uu____763  in
                    uu____616 :: uu____675  in
                  uu____535 :: uu____593  in
                let mk1 l v1 =
                  let uu____3115 =
                    let uu____3127 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____3217  ->
                              match uu____3217 with
                              | (l',uu____3238) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3127
                      (FStar_Option.map
                         (fun uu____3337  ->
                            match uu____3337 with
                            | (uu____3365,b) ->
                                let uu____3399 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3399 v1))
                     in
                  FStar_All.pipe_right uu____3115 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____3482  ->
                          match uu____3482 with
                          | (l',uu____3503) -> FStar_Ident.lid_equals l l'))
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
          let uu____3577 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3577 with
          | (xxsym,xx) ->
              let uu____3588 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____3588 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____3604 =
                     let uu____3612 =
                       let uu____3613 =
                         let uu____3624 =
                           let uu____3625 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____3635 =
                             let uu____3646 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____3646 :: vars  in
                           uu____3625 :: uu____3635  in
                         let uu____3672 =
                           let uu____3673 =
                             let uu____3678 =
                               let uu____3679 =
                                 let uu____3684 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3684)  in
                               FStar_SMTEncoding_Util.mkEq uu____3679  in
                             (xx_has_type, uu____3678)  in
                           FStar_SMTEncoding_Util.mkImp uu____3673  in
                         ([[xx_has_type]], uu____3624, uu____3672)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____3613  in
                     let uu____3697 =
                       let uu____3699 =
                         let uu____3701 =
                           let uu____3703 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____3703  in
                         Prims.op_Hat module_name uu____3701  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3699
                        in
                     (uu____3612, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3697)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____3604)
  
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
    let uu____3759 =
      let uu____3761 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____3761  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3759  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3783 =
      let uu____3784 =
        let uu____3792 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3792, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3784  in
    let uu____3797 =
      let uu____3800 =
        let uu____3801 =
          let uu____3809 =
            let uu____3810 =
              let uu____3821 =
                let uu____3822 =
                  let uu____3827 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3827)  in
                FStar_SMTEncoding_Util.mkImp uu____3822  in
              ([[typing_pred]], [xx], uu____3821)  in
            let uu____3852 =
              let uu____3867 = FStar_TypeChecker_Env.get_range env  in
              let uu____3868 = mkForall_fuel1 env  in uu____3868 uu____3867
               in
            uu____3852 uu____3810  in
          (uu____3809, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3801  in
      [uu____3800]  in
    uu____3783 :: uu____3797  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3915 =
      let uu____3916 =
        let uu____3924 =
          let uu____3925 = FStar_TypeChecker_Env.get_range env  in
          let uu____3926 =
            let uu____3937 =
              let uu____3942 =
                let uu____3945 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3945]  in
              [uu____3942]  in
            let uu____3950 =
              let uu____3951 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3951 tt  in
            (uu____3937, [bb], uu____3950)  in
          FStar_SMTEncoding_Term.mkForall uu____3925 uu____3926  in
        (uu____3924, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3916  in
    let uu____3976 =
      let uu____3979 =
        let uu____3980 =
          let uu____3988 =
            let uu____3989 =
              let uu____4000 =
                let uu____4001 =
                  let uu____4006 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____4006)  in
                FStar_SMTEncoding_Util.mkImp uu____4001  in
              ([[typing_pred]], [xx], uu____4000)  in
            let uu____4033 =
              let uu____4048 = FStar_TypeChecker_Env.get_range env  in
              let uu____4049 = mkForall_fuel1 env  in uu____4049 uu____4048
               in
            uu____4033 uu____3989  in
          (uu____3988, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3980  in
      [uu____3979]  in
    uu____3915 :: uu____3976  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____4092 =
        let uu____4093 =
          let uu____4099 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4099, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4093  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4092  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4113 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4113  in
    let uu____4118 =
      let uu____4119 =
        let uu____4127 =
          let uu____4128 = FStar_TypeChecker_Env.get_range env  in
          let uu____4129 =
            let uu____4140 =
              let uu____4145 =
                let uu____4148 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4148]  in
              [uu____4145]  in
            let uu____4153 =
              let uu____4154 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4154 tt  in
            (uu____4140, [bb], uu____4153)  in
          FStar_SMTEncoding_Term.mkForall uu____4128 uu____4129  in
        (uu____4127, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4119  in
    let uu____4179 =
      let uu____4182 =
        let uu____4183 =
          let uu____4191 =
            let uu____4192 =
              let uu____4203 =
                let uu____4204 =
                  let uu____4209 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4209)  in
                FStar_SMTEncoding_Util.mkImp uu____4204  in
              ([[typing_pred]], [xx], uu____4203)  in
            let uu____4236 =
              let uu____4251 = FStar_TypeChecker_Env.get_range env  in
              let uu____4252 = mkForall_fuel1 env  in uu____4252 uu____4251
               in
            uu____4236 uu____4192  in
          (uu____4191, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4183  in
      let uu____4274 =
        let uu____4277 =
          let uu____4278 =
            let uu____4286 =
              let uu____4287 =
                let uu____4298 =
                  let uu____4299 =
                    let uu____4304 =
                      let uu____4305 =
                        let uu____4308 =
                          let uu____4311 =
                            let uu____4314 =
                              let uu____4315 =
                                let uu____4320 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4321 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____4320, uu____4321)  in
                              FStar_SMTEncoding_Util.mkGT uu____4315  in
                            let uu____4323 =
                              let uu____4326 =
                                let uu____4327 =
                                  let uu____4332 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4333 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____4332, uu____4333)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4327  in
                              let uu____4335 =
                                let uu____4338 =
                                  let uu____4339 =
                                    let uu____4344 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4345 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4344, uu____4345)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4339  in
                                [uu____4338]  in
                              uu____4326 :: uu____4335  in
                            uu____4314 :: uu____4323  in
                          typing_pred_y :: uu____4311  in
                        typing_pred :: uu____4308  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4305  in
                    (uu____4304, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4299  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4298)
                 in
              let uu____4378 =
                let uu____4393 = FStar_TypeChecker_Env.get_range env  in
                let uu____4394 = mkForall_fuel1 env  in uu____4394 uu____4393
                 in
              uu____4378 uu____4287  in
            (uu____4286,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4278  in
        [uu____4277]  in
      uu____4182 :: uu____4274  in
    uu____4118 :: uu____4179  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____4437 =
        let uu____4438 =
          let uu____4444 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4444, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4438  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4437  in
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
      let uu____4460 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4460  in
    let uu____4465 =
      let uu____4466 =
        let uu____4474 =
          let uu____4475 = FStar_TypeChecker_Env.get_range env  in
          let uu____4476 =
            let uu____4487 =
              let uu____4492 =
                let uu____4495 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4495]  in
              [uu____4492]  in
            let uu____4500 =
              let uu____4501 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4501 tt  in
            (uu____4487, [bb], uu____4500)  in
          FStar_SMTEncoding_Term.mkForall uu____4475 uu____4476  in
        (uu____4474, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4466  in
    let uu____4526 =
      let uu____4529 =
        let uu____4530 =
          let uu____4538 =
            let uu____4539 =
              let uu____4550 =
                let uu____4551 =
                  let uu____4556 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____4556)  in
                FStar_SMTEncoding_Util.mkImp uu____4551  in
              ([[typing_pred]], [xx], uu____4550)  in
            let uu____4583 =
              let uu____4598 = FStar_TypeChecker_Env.get_range env  in
              let uu____4599 = mkForall_fuel1 env  in uu____4599 uu____4598
               in
            uu____4583 uu____4539  in
          (uu____4538, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4530  in
      let uu____4621 =
        let uu____4624 =
          let uu____4625 =
            let uu____4633 =
              let uu____4634 =
                let uu____4645 =
                  let uu____4646 =
                    let uu____4651 =
                      let uu____4652 =
                        let uu____4655 =
                          let uu____4658 =
                            let uu____4661 =
                              let uu____4662 =
                                let uu____4667 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____4668 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____4667, uu____4668)  in
                              FStar_SMTEncoding_Util.mkGT uu____4662  in
                            let uu____4670 =
                              let uu____4673 =
                                let uu____4674 =
                                  let uu____4679 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____4680 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____4679, uu____4680)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4674  in
                              let uu____4682 =
                                let uu____4685 =
                                  let uu____4686 =
                                    let uu____4691 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____4692 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____4691, uu____4692)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4686  in
                                [uu____4685]  in
                              uu____4673 :: uu____4682  in
                            uu____4661 :: uu____4670  in
                          typing_pred_y :: uu____4658  in
                        typing_pred :: uu____4655  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4652  in
                    (uu____4651, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4646  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4645)
                 in
              let uu____4725 =
                let uu____4740 = FStar_TypeChecker_Env.get_range env  in
                let uu____4741 = mkForall_fuel1 env  in uu____4741 uu____4740
                 in
              uu____4725 uu____4634  in
            (uu____4633,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4625  in
        [uu____4624]  in
      uu____4529 :: uu____4621  in
    uu____4465 :: uu____4526  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4788 =
      let uu____4789 =
        let uu____4797 =
          let uu____4798 = FStar_TypeChecker_Env.get_range env  in
          let uu____4799 =
            let uu____4810 =
              let uu____4815 =
                let uu____4818 = FStar_SMTEncoding_Term.boxString b  in
                [uu____4818]  in
              [uu____4815]  in
            let uu____4823 =
              let uu____4824 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4824 tt  in
            (uu____4810, [bb], uu____4823)  in
          FStar_SMTEncoding_Term.mkForall uu____4798 uu____4799  in
        (uu____4797, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4789  in
    let uu____4849 =
      let uu____4852 =
        let uu____4853 =
          let uu____4861 =
            let uu____4862 =
              let uu____4873 =
                let uu____4874 =
                  let uu____4879 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____4879)  in
                FStar_SMTEncoding_Util.mkImp uu____4874  in
              ([[typing_pred]], [xx], uu____4873)  in
            let uu____4906 =
              let uu____4921 = FStar_TypeChecker_Env.get_range env  in
              let uu____4922 = mkForall_fuel1 env  in uu____4922 uu____4921
               in
            uu____4906 uu____4862  in
          (uu____4861, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4853  in
      [uu____4852]  in
    uu____4788 :: uu____4849  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____4969 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____4969]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____4999 =
      let uu____5000 =
        let uu____5008 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____5008, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5000  in
    [uu____4999]  in
  let mk_and_interp env conj uu____5031 =
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
    let uu____5060 =
      let uu____5061 =
        let uu____5069 =
          let uu____5070 = FStar_TypeChecker_Env.get_range env  in
          let uu____5071 =
            let uu____5082 =
              let uu____5083 =
                let uu____5088 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____5088, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5083  in
            ([[l_and_a_b]], [aa; bb], uu____5082)  in
          FStar_SMTEncoding_Term.mkForall uu____5070 uu____5071  in
        (uu____5069, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5061  in
    [uu____5060]  in
  let mk_or_interp env disj uu____5143 =
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
    let uu____5172 =
      let uu____5173 =
        let uu____5181 =
          let uu____5182 = FStar_TypeChecker_Env.get_range env  in
          let uu____5183 =
            let uu____5194 =
              let uu____5195 =
                let uu____5200 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5200, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5195  in
            ([[l_or_a_b]], [aa; bb], uu____5194)  in
          FStar_SMTEncoding_Term.mkForall uu____5182 uu____5183  in
        (uu____5181, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5173  in
    [uu____5172]  in
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
    let uu____5278 =
      let uu____5279 =
        let uu____5287 =
          let uu____5288 = FStar_TypeChecker_Env.get_range env  in
          let uu____5289 =
            let uu____5300 =
              let uu____5301 =
                let uu____5306 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5306, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5301  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5300)  in
          FStar_SMTEncoding_Term.mkForall uu____5288 uu____5289  in
        (uu____5287, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5279  in
    [uu____5278]  in
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
    let uu____5396 =
      let uu____5397 =
        let uu____5405 =
          let uu____5406 = FStar_TypeChecker_Env.get_range env  in
          let uu____5407 =
            let uu____5418 =
              let uu____5419 =
                let uu____5424 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5424, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5419  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5418)  in
          FStar_SMTEncoding_Term.mkForall uu____5406 uu____5407  in
        (uu____5405, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5397  in
    [uu____5396]  in
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
    let uu____5524 =
      let uu____5525 =
        let uu____5533 =
          let uu____5534 = FStar_TypeChecker_Env.get_range env  in
          let uu____5535 =
            let uu____5546 =
              let uu____5547 =
                let uu____5552 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____5552, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5547  in
            ([[l_imp_a_b]], [aa; bb], uu____5546)  in
          FStar_SMTEncoding_Term.mkForall uu____5534 uu____5535  in
        (uu____5533, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5525  in
    [uu____5524]  in
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
    let uu____5636 =
      let uu____5637 =
        let uu____5645 =
          let uu____5646 = FStar_TypeChecker_Env.get_range env  in
          let uu____5647 =
            let uu____5658 =
              let uu____5659 =
                let uu____5664 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____5664, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5659  in
            ([[l_iff_a_b]], [aa; bb], uu____5658)  in
          FStar_SMTEncoding_Term.mkForall uu____5646 uu____5647  in
        (uu____5645, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5637  in
    [uu____5636]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____5735 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____5735  in
    let uu____5740 =
      let uu____5741 =
        let uu____5749 =
          let uu____5750 = FStar_TypeChecker_Env.get_range env  in
          let uu____5751 =
            let uu____5762 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____5762)  in
          FStar_SMTEncoding_Term.mkForall uu____5750 uu____5751  in
        (uu____5749, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5741  in
    [uu____5740]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____5815 =
      let uu____5816 =
        let uu____5824 =
          let uu____5825 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____5825 range_ty  in
        let uu____5826 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____5824, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____5826)
         in
      FStar_SMTEncoding_Util.mkAssume uu____5816  in
    [uu____5815]  in
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
        let uu____5872 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____5872 x1 t  in
      let uu____5874 = FStar_TypeChecker_Env.get_range env  in
      let uu____5875 =
        let uu____5886 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____5886)  in
      FStar_SMTEncoding_Term.mkForall uu____5874 uu____5875  in
    let uu____5911 =
      let uu____5912 =
        let uu____5920 =
          let uu____5921 = FStar_TypeChecker_Env.get_range env  in
          let uu____5922 =
            let uu____5933 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____5933)  in
          FStar_SMTEncoding_Term.mkForall uu____5921 uu____5922  in
        (uu____5920,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5912  in
    [uu____5911]  in
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
    let uu____5994 =
      let uu____5995 =
        let uu____6003 =
          let uu____6004 = FStar_TypeChecker_Env.get_range env  in
          let uu____6005 =
            let uu____6021 =
              let uu____6022 =
                let uu____6027 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____6028 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____6027, uu____6028)  in
              FStar_SMTEncoding_Util.mkAnd uu____6022  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____6021)
             in
          FStar_SMTEncoding_Term.mkForall' uu____6004 uu____6005  in
        (uu____6003,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5995  in
    [uu____5994]  in
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
          let uu____6586 =
            FStar_Util.find_opt
              (fun uu____6624  ->
                 match uu____6624 with
                 | (l,uu____6640) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____6586 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____6683,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____6744 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____6744 with
        | (form,decls) ->
            let uu____6753 =
              let uu____6756 =
                let uu____6759 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____6759]  in
              FStar_All.pipe_right uu____6756
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____6753
  
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
              let uu____6818 =
                ((let uu____6822 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____6822) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____6818
              then
                let arg_sorts =
                  let uu____6834 =
                    let uu____6835 = FStar_Syntax_Subst.compress t_norm  in
                    uu____6835.FStar_Syntax_Syntax.n  in
                  match uu____6834 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6841) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6879  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6886 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6888 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6888 with
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
                    let uu____6920 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____6920, env1)
              else
                (let uu____6925 = prims.is lid  in
                 if uu____6925
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6934 = prims.mk lid vname  in
                   match uu____6934 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____6958 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____6958, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6967 =
                      let uu____6986 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____6986 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7014 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7014
                            then
                              let uu____7019 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___292_7022 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___292_7022.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___292_7022.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___292_7022.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___292_7022.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___292_7022.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___292_7022.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___292_7022.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___292_7022.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___292_7022.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___292_7022.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___292_7022.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___292_7022.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___292_7022.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___292_7022.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___292_7022.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___292_7022.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___292_7022.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___292_7022.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___292_7022.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___292_7022.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___292_7022.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___292_7022.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___292_7022.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___292_7022.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___292_7022.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___292_7022.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___292_7022.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___292_7022.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___292_7022.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___292_7022.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___292_7022.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___292_7022.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___292_7022.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___292_7022.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___292_7022.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___292_7022.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___292_7022.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___292_7022.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___292_7022.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___292_7022.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___292_7022.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___292_7022.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7019
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7045 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____7045)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6967 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_7151  ->
                                  match uu___0_7151 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7155 = FStar_Util.prefix vars
                                         in
                                      (match uu____7155 with
                                       | (uu____7188,xxv) ->
                                           let xx =
                                             let uu____7227 =
                                               let uu____7228 =
                                                 let uu____7234 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7234,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7228
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7227
                                              in
                                           let uu____7237 =
                                             let uu____7238 =
                                               let uu____7246 =
                                                 let uu____7247 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7248 =
                                                   let uu____7259 =
                                                     let uu____7260 =
                                                       let uu____7265 =
                                                         let uu____7266 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7266
                                                          in
                                                       (vapp, uu____7265)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7260
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7259)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7247 uu____7248
                                                  in
                                               (uu____7246,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7238
                                              in
                                           [uu____7237])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7281 = FStar_Util.prefix vars
                                         in
                                      (match uu____7281 with
                                       | (uu____7314,xxv) ->
                                           let xx =
                                             let uu____7353 =
                                               let uu____7354 =
                                                 let uu____7360 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7360,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7354
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7353
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
                                           let uu____7371 =
                                             let uu____7372 =
                                               let uu____7380 =
                                                 let uu____7381 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7382 =
                                                   let uu____7393 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7393)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7381 uu____7382
                                                  in
                                               (uu____7380,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7372
                                              in
                                           [uu____7371])
                                  | uu____7406 -> []))
                           in
                        let uu____7407 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7407 with
                         | (vars,guards,env',decls1,uu____7432) ->
                             let uu____7445 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7458 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7458, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7462 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7462 with
                                    | (g,ds) ->
                                        let uu____7475 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7475,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7445 with
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
                                  let should_thunk uu____7498 =
                                    let is_type1 t =
                                      let uu____7506 =
                                        let uu____7507 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7507.FStar_Syntax_Syntax.n  in
                                      match uu____7506 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7511 -> true
                                      | uu____7513 -> false  in
                                    let is_squash1 t =
                                      let uu____7522 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____7522 with
                                      | (head1,uu____7541) ->
                                          let uu____7566 =
                                            let uu____7567 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____7567.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7566 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____7572;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____7573;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____7575;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____7576;_};_},uu____7577)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____7585 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____7590 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____7590))
                                       &&
                                       (let uu____7596 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____7596))
                                      &&
                                      (let uu____7599 = is_type1 t_norm  in
                                       Prims.op_Negation uu____7599)
                                     in
                                  let uu____7601 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____7660 -> (false, vars)  in
                                  (match uu____7601 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____7710 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____7710 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____7742 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____7751 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____7751
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____7762 ->
                                                  let uu____7771 =
                                                    let uu____7779 =
                                                      get_vtok ()  in
                                                    (uu____7779, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7771
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____7786 =
                                                let uu____7794 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____7794)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____7786
                                               in
                                            let uu____7808 =
                                              let vname_decl =
                                                let uu____7816 =
                                                  let uu____7828 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____7828,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____7816
                                                 in
                                              let uu____7839 =
                                                let env2 =
                                                  let uu___387_7845 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___387_7845.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____7846 =
                                                  let uu____7848 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____7848
                                                   in
                                                if uu____7846
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____7839 with
                                              | (tok_typing,decls2) ->
                                                  let uu____7865 =
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
                                                        let uu____7891 =
                                                          let uu____7894 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____7894
                                                           in
                                                        let uu____7901 =
                                                          let uu____7902 =
                                                            let uu____7905 =
                                                              let uu____7906
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____7906
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _7910  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _7910)
                                                              uu____7905
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____7902
                                                           in
                                                        (uu____7891,
                                                          uu____7901)
                                                    | uu____7913 when thunked
                                                        ->
                                                        let uu____7924 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____7924
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____7939
                                                                 =
                                                                 let uu____7947
                                                                   =
                                                                   let uu____7950
                                                                    =
                                                                    let uu____7953
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____7953]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____7950
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____7947)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____7939
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____7961 =
                                                               let uu____7969
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____7969,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7961
                                                              in
                                                           let uu____7974 =
                                                             let uu____7977 =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____7977
                                                              in
                                                           (uu____7974, env1))
                                                    | uu____7986 ->
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
                                                          let uu____8010 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____8011 =
                                                            let uu____8022 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____8022)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____8010
                                                            uu____8011
                                                           in
                                                        let name_tok_corr =
                                                          let uu____8032 =
                                                            let uu____8040 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____8040,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8032
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
                                                            let uu____8051 =
                                                              let uu____8052
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8052]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8051
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8079 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8080 =
                                                              let uu____8091
                                                                =
                                                                let uu____8092
                                                                  =
                                                                  let uu____8097
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8098
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8097,
                                                                    uu____8098)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8092
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8091)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8079
                                                              uu____8080
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8127 =
                                                          let uu____8130 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8130
                                                           in
                                                        (uu____8127, env1)
                                                     in
                                                  (match uu____7865 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8151 =
                                                         let uu____8154 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8154
                                                           tok_decl
                                                          in
                                                       (uu____8151, env2))
                                               in
                                            (match uu____7808 with
                                             | (decls2,env2) ->
                                                 let uu____8173 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8183 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8183 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8198 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8198, decls)
                                                    in
                                                 (match uu____8173 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8213 =
                                                          let uu____8221 =
                                                            let uu____8222 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8223 =
                                                              let uu____8234
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8234)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8222
                                                              uu____8223
                                                             in
                                                          (uu____8221,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8213
                                                         in
                                                      let freshness =
                                                        let uu____8250 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8250
                                                        then
                                                          let uu____8258 =
                                                            let uu____8259 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8260 =
                                                              let uu____8273
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8280
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8273,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8280)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8259
                                                              uu____8260
                                                             in
                                                          let uu____8286 =
                                                            let uu____8289 =
                                                              let uu____8290
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8290
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8289]  in
                                                          uu____8258 ::
                                                            uu____8286
                                                        else []  in
                                                      let g =
                                                        let uu____8296 =
                                                          let uu____8299 =
                                                            let uu____8302 =
                                                              let uu____8305
                                                                =
                                                                let uu____8308
                                                                  =
                                                                  let uu____8311
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8311
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8308
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8305
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8302
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8299
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8296
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
          let uu____8351 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8351 with
          | FStar_Pervasives_Native.None  ->
              let uu____8362 = encode_free_var false env x t t_norm []  in
              (match uu____8362 with
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
            let uu____8425 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8425 with
            | (decls,env1) ->
                let uu____8436 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8436
                then
                  let uu____8443 =
                    let uu____8444 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8444  in
                  (uu____8443, env1)
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
             (fun uu____8500  ->
                fun lb  ->
                  match uu____8500 with
                  | (decls,env1) ->
                      let uu____8520 =
                        let uu____8525 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8525
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8520 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8554 = FStar_Syntax_Util.head_and_args t  in
    match uu____8554 with
    | (hd1,args) ->
        let uu____8598 =
          let uu____8599 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8599.FStar_Syntax_Syntax.n  in
        (match uu____8598 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8605,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____8629 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____8640 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___474_8648 = en  in
    let uu____8649 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___474_8648.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___474_8648.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___474_8648.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___474_8648.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___474_8648.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___474_8648.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___474_8648.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___474_8648.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___474_8648.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___474_8648.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____8649
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____8679  ->
      fun quals  ->
        match uu____8679 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8784 = FStar_Util.first_N nbinders formals  in
              match uu____8784 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____8881  ->
                         fun uu____8882  ->
                           match (uu____8881, uu____8882) with
                           | ((formal,uu____8908),(binder,uu____8910)) ->
                               let uu____8931 =
                                 let uu____8938 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____8938)  in
                               FStar_Syntax_Syntax.NT uu____8931) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____8952 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8993  ->
                              match uu____8993 with
                              | (x,i) ->
                                  let uu____9012 =
                                    let uu___500_9013 = x  in
                                    let uu____9014 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___500_9013.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___500_9013.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9014
                                    }  in
                                  (uu____9012, i)))
                       in
                    FStar_All.pipe_right uu____8952
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9038 =
                      let uu____9043 = FStar_Syntax_Subst.compress body  in
                      let uu____9044 =
                        let uu____9045 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9045
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____9043 uu____9044
                       in
                    uu____9038 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___507_9094 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___507_9094.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___507_9094.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___507_9094.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___507_9094.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___507_9094.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___507_9094.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___507_9094.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___507_9094.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___507_9094.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___507_9094.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___507_9094.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___507_9094.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___507_9094.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___507_9094.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___507_9094.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___507_9094.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___507_9094.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___507_9094.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___507_9094.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___507_9094.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___507_9094.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___507_9094.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___507_9094.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___507_9094.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___507_9094.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___507_9094.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___507_9094.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___507_9094.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___507_9094.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___507_9094.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___507_9094.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___507_9094.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___507_9094.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___507_9094.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___507_9094.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___507_9094.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___507_9094.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___507_9094.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___507_9094.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___507_9094.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___507_9094.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___507_9094.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____9166  ->
                       fun uu____9167  ->
                         match (uu____9166, uu____9167) with
                         | ((x,uu____9193),(b,uu____9195)) ->
                             let uu____9216 =
                               let uu____9223 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9223)  in
                             FStar_Syntax_Syntax.NT uu____9216) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9248 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9248
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9277 ->
                    let uu____9284 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9284
                | uu____9285 when Prims.op_Negation norm1 ->
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
                | uu____9288 ->
                    let uu____9289 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9289)
                 in
              let aux t1 e1 =
                let uu____9331 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9331 with
                | (binders,body,lopt) ->
                    let uu____9363 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9379 -> arrow_formals_comp_norm false t1  in
                    (match uu____9363 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9413 =
                           if nformals < nbinders
                           then
                             let uu____9447 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9447 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9527 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9527)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9557 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9557 with
                                | (binders1,body1) ->
                                    let uu____9610 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____9610))
                             else
                               (let uu____9623 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____9623))
                            in
                         (match uu____9413 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____9683 = aux t e  in
              match uu____9683 with
              | (binders,body,comp) ->
                  let uu____9729 =
                    let uu____9740 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____9740
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____9755 = aux comp1 body1  in
                      match uu____9755 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____9729 with
                   | (binders1,body1,comp1) ->
                       let uu____9838 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____9838, comp1))
               in
            (try
               (fun uu___577_9865  ->
                  match () with
                  | () ->
                      let uu____9872 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9872
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9888 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9951  ->
                                   fun lb  ->
                                     match uu____9951 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____10006 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____10006
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____10012 =
                                             let uu____10021 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____10021
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____10012 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9888 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10162;
                                    FStar_Syntax_Syntax.lbeff = uu____10163;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10165;
                                    FStar_Syntax_Syntax.lbpos = uu____10166;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10190 =
                                     let uu____10197 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10197 with
                                     | (tcenv',uu____10213,e_t) ->
                                         let uu____10219 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10230 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10219 with
                                          | (e1,t_norm1) ->
                                              ((let uu___640_10247 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___640_10247.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10190 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10257 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10257 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10277 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10277
                                               then
                                                 let uu____10282 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10285 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10282 uu____10285
                                               else ());
                                              (let uu____10290 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10290 with
                                               | (vars,_guards,env'1,binder_decls,uu____10317)
                                                   ->
                                                   let uu____10330 =
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
                                                         let uu____10347 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10347
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10369 =
                                                          let uu____10370 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10371 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10370 fvb
                                                            uu____10371
                                                           in
                                                        (vars, uu____10369))
                                                      in
                                                   (match uu____10330 with
                                                    | (vars1,app) ->
                                                        let uu____10382 =
                                                          let is_logical =
                                                            let uu____10395 =
                                                              let uu____10396
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10396.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10395
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10402 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10406 =
                                                              let uu____10407
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10407
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10406
                                                              (fun lid  ->
                                                                 let uu____10416
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10416
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10417 =
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
                                                          if uu____10417
                                                          then
                                                            let uu____10433 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10434 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10433,
                                                              uu____10434)
                                                          else
                                                            (let uu____10445
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10445))
                                                           in
                                                        (match uu____10382
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10469
                                                                 =
                                                                 let uu____10477
                                                                   =
                                                                   let uu____10478
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10479
                                                                    =
                                                                    let uu____10490
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10490)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10478
                                                                    uu____10479
                                                                    in
                                                                 let uu____10499
                                                                   =
                                                                   let uu____10500
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10500
                                                                    in
                                                                 (uu____10477,
                                                                   uu____10499,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10469
                                                                in
                                                             let uu____10506
                                                               =
                                                               let uu____10509
                                                                 =
                                                                 let uu____10512
                                                                   =
                                                                   let uu____10515
                                                                    =
                                                                    let uu____10518
                                                                    =
                                                                    let uu____10521
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10521
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10518
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10515
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10512
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10509
                                                                in
                                                             (uu____10506,
                                                               env2)))))))
                               | uu____10530 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10590 =
                                   let uu____10596 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____10596,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10590  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10602 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10655  ->
                                         fun fvb  ->
                                           match uu____10655 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10710 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10710
                                                  in
                                               let gtok =
                                                 let uu____10714 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10714
                                                  in
                                               let env4 =
                                                 let uu____10717 =
                                                   let uu____10720 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _10726  ->
                                                        FStar_Pervasives_Native.Some
                                                          _10726) uu____10720
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10717
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10602 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10846
                                     t_norm uu____10848 =
                                     match (uu____10846, uu____10848) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10878;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10879;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10881;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10882;_})
                                         ->
                                         let uu____10909 =
                                           let uu____10916 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10916 with
                                           | (tcenv',uu____10932,e_t) ->
                                               let uu____10938 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10949 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10938 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___727_10966 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___727_10966.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10909 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10979 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10979
                                                then
                                                  let uu____10984 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10986 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10988 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10984 uu____10986
                                                    uu____10988
                                                else ());
                                               (let uu____10993 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____10993 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____11020 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____11020 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11042 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11042
                                                           then
                                                             let uu____11047
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11049
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11052
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11054
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11047
                                                               uu____11049
                                                               uu____11052
                                                               uu____11054
                                                           else ());
                                                          (let uu____11059 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11059
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11088)
                                                               ->
                                                               let uu____11101
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11114
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11114,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11118
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11118
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11131
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11131,
                                                                    decls0))
                                                                  in
                                                               (match uu____11101
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
                                                                    let uu____11152
                                                                    =
                                                                    let uu____11164
                                                                    =
                                                                    let uu____11167
                                                                    =
                                                                    let uu____11170
                                                                    =
                                                                    let uu____11173
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11173
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11170
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11167
                                                                     in
                                                                    (g,
                                                                    uu____11164,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11152
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
                                                                    let uu____11203
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11203
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
                                                                    let uu____11218
                                                                    =
                                                                    let uu____11221
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11221
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11218
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11227
                                                                    =
                                                                    let uu____11230
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11230
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11227
                                                                     in
                                                                    let uu____11235
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11235
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11251
                                                                    =
                                                                    let uu____11259
                                                                    =
                                                                    let uu____11260
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11261
                                                                    =
                                                                    let uu____11277
                                                                    =
                                                                    let uu____11278
                                                                    =
                                                                    let uu____11283
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11283)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11278
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11277)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11260
                                                                    uu____11261
                                                                     in
                                                                    let uu____11297
                                                                    =
                                                                    let uu____11298
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11298
                                                                     in
                                                                    (uu____11259,
                                                                    uu____11297,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11251
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11305
                                                                    =
                                                                    let uu____11313
                                                                    =
                                                                    let uu____11314
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11315
                                                                    =
                                                                    let uu____11326
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11326)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11314
                                                                    uu____11315
                                                                     in
                                                                    (uu____11313,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11305
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11340
                                                                    =
                                                                    let uu____11348
                                                                    =
                                                                    let uu____11349
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11350
                                                                    =
                                                                    let uu____11361
                                                                    =
                                                                    let uu____11362
                                                                    =
                                                                    let uu____11367
                                                                    =
                                                                    let uu____11368
                                                                    =
                                                                    let uu____11371
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11371
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11368
                                                                     in
                                                                    (gsapp,
                                                                    uu____11367)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11362
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11361)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11349
                                                                    uu____11350
                                                                     in
                                                                    (uu____11348,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11340
                                                                     in
                                                                    let uu____11385
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
                                                                    let uu____11397
                                                                    =
                                                                    let uu____11398
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11398
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11397
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____11400
                                                                    =
                                                                    let uu____11408
                                                                    =
                                                                    let uu____11409
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11410
                                                                    =
                                                                    let uu____11421
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11421)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11409
                                                                    uu____11410
                                                                     in
                                                                    (uu____11408,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11400
                                                                     in
                                                                    let uu____11434
                                                                    =
                                                                    let uu____11443
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11443
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11458
                                                                    =
                                                                    let uu____11461
                                                                    =
                                                                    let uu____11462
                                                                    =
                                                                    let uu____11470
                                                                    =
                                                                    let uu____11471
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11472
                                                                    =
                                                                    let uu____11483
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11483)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11471
                                                                    uu____11472
                                                                     in
                                                                    (uu____11470,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11462
                                                                     in
                                                                    [uu____11461]
                                                                     in
                                                                    (d3,
                                                                    uu____11458)
                                                                     in
                                                                    match uu____11434
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11385
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11540
                                                                    =
                                                                    let uu____11543
                                                                    =
                                                                    let uu____11546
                                                                    =
                                                                    let uu____11549
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11549
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11546
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11543
                                                                     in
                                                                    let uu____11556
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11540,
                                                                    uu____11556,
                                                                    env02))))))))))
                                      in
                                   let uu____11561 =
                                     let uu____11574 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11637  ->
                                          fun uu____11638  ->
                                            match (uu____11637, uu____11638)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11763 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11763 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11574
                                      in
                                   (match uu____11561 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11830 =
                                          let isDeclFun uu___1_11847 =
                                            match uu___1_11847 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11849 -> true
                                            | uu____11862 -> false  in
                                          let uu____11864 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11864
                                            (fun decls3  ->
                                               let uu____11894 =
                                                 FStar_List.fold_left
                                                   (fun uu____11925  ->
                                                      fun elt  ->
                                                        match uu____11925
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____11966 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____11966
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____11994
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____11994
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
                                                                    let uu___820_12032
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___820_12032.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___820_12032.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___820_12032.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____11894 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12064 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12064, elts, rest))
                                           in
                                        (match uu____11830 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12093 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12099  ->
                                        match uu___2_12099 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12102 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12110 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12110)))
                                in
                             if uu____12093
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___837_12132  ->
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
                   let uu____12171 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12171
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12190 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12190, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12246 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12246 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12252 = encode_sigelt' env se  in
      match uu____12252 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12264 =
                  let uu____12267 =
                    let uu____12268 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12268  in
                  [uu____12267]  in
                FStar_All.pipe_right uu____12264
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12273 ->
                let uu____12274 =
                  let uu____12277 =
                    let uu____12280 =
                      let uu____12281 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12281  in
                    [uu____12280]  in
                  FStar_All.pipe_right uu____12277
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12288 =
                  let uu____12291 =
                    let uu____12294 =
                      let uu____12297 =
                        let uu____12298 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12298  in
                      [uu____12297]  in
                    FStar_All.pipe_right uu____12294
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12291  in
                FStar_List.append uu____12274 uu____12288
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12312 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12312
       then
         let uu____12317 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12317
       else ());
      (let is_opaque_to_smt t =
         let uu____12329 =
           let uu____12330 = FStar_Syntax_Subst.compress t  in
           uu____12330.FStar_Syntax_Syntax.n  in
         match uu____12329 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12335)) -> s = "opaque_to_smt"
         | uu____12340 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12349 =
           let uu____12350 = FStar_Syntax_Subst.compress t  in
           uu____12350.FStar_Syntax_Syntax.n  in
         match uu____12349 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12355)) -> s = "uninterpreted_by_smt"
         | uu____12360 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12366 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12372 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12384 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12385 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12386 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12399 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12401 =
             let uu____12403 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12403  in
           if uu____12401
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12432 ->
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
                let uu____12464 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12464 with
                | (formals,uu____12484) ->
                    let arity = FStar_List.length formals  in
                    let uu____12508 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12508 with
                     | (aname,atok,env2) ->
                         let uu____12530 =
                           let uu____12535 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____12535 env2
                            in
                         (match uu____12530 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12547 =
                                  let uu____12548 =
                                    let uu____12560 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____12580  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12560,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12548
                                   in
                                [uu____12547;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____12597 =
                                let aux uu____12643 uu____12644 =
                                  match (uu____12643, uu____12644) with
                                  | ((bv,uu____12688),(env3,acc_sorts,acc))
                                      ->
                                      let uu____12720 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____12720 with
                                       | (xxsym,xx,env4) ->
                                           let uu____12743 =
                                             let uu____12746 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____12746 :: acc_sorts  in
                                           (env4, uu____12743, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____12597 with
                               | (uu____12778,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____12794 =
                                       let uu____12802 =
                                         let uu____12803 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12804 =
                                           let uu____12815 =
                                             let uu____12816 =
                                               let uu____12821 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____12821)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____12816
                                              in
                                           ([[app]], xs_sorts, uu____12815)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12803 uu____12804
                                          in
                                       (uu____12802,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12794
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____12836 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____12836
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____12839 =
                                       let uu____12847 =
                                         let uu____12848 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12849 =
                                           let uu____12860 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____12860)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12848 uu____12849
                                          in
                                       (uu____12847,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12839
                                      in
                                   let uu____12873 =
                                     let uu____12876 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____12876  in
                                   (env2, uu____12873))))
                 in
              let uu____12885 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____12885 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12911,uu____12912)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____12913 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____12913 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12935,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____12942 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_12948  ->
                       match uu___3_12948 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____12951 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____12957 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____12960 -> false))
                in
             Prims.op_Negation uu____12942  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____12970 =
                let uu____12975 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____12975 env fv t quals  in
              match uu____12970 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____12989 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____12989  in
                  let uu____12992 =
                    let uu____12993 =
                      let uu____12996 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____12996
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____12993  in
                  (uu____12992, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13006 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13006 with
            | (uvs,f1) ->
                let env1 =
                  let uu___973_13018 = env  in
                  let uu____13019 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___973_13018.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___973_13018.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___973_13018.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13019;
                    FStar_SMTEncoding_Env.warn =
                      (uu___973_13018.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___973_13018.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___973_13018.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___973_13018.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___973_13018.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___973_13018.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___973_13018.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____13021 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13021 with
                 | (f3,decls) ->
                     let g =
                       let uu____13035 =
                         let uu____13038 =
                           let uu____13039 =
                             let uu____13047 =
                               let uu____13048 =
                                 let uu____13050 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13050
                                  in
                               FStar_Pervasives_Native.Some uu____13048  in
                             let uu____13054 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13047, uu____13054)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13039  in
                         [uu____13038]  in
                       FStar_All.pipe_right uu____13035
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13063) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13077 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13099 =
                        let uu____13102 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13102.FStar_Syntax_Syntax.fv_name  in
                      uu____13099.FStar_Syntax_Syntax.v  in
                    let uu____13103 =
                      let uu____13105 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13105  in
                    if uu____13103
                    then
                      let val_decl =
                        let uu___990_13137 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___990_13137.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___990_13137.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___990_13137.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____13138 = encode_sigelt' env1 val_decl  in
                      match uu____13138 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13077 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13174,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13176;
                           FStar_Syntax_Syntax.lbtyp = uu____13177;
                           FStar_Syntax_Syntax.lbeff = uu____13178;
                           FStar_Syntax_Syntax.lbdef = uu____13179;
                           FStar_Syntax_Syntax.lbattrs = uu____13180;
                           FStar_Syntax_Syntax.lbpos = uu____13181;_}::[]),uu____13182)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13201 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____13201 with
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
                  let uu____13239 =
                    let uu____13242 =
                      let uu____13243 =
                        let uu____13251 =
                          let uu____13252 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13253 =
                            let uu____13264 =
                              let uu____13265 =
                                let uu____13270 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13270)  in
                              FStar_SMTEncoding_Util.mkEq uu____13265  in
                            ([[b2t_x]], [xx], uu____13264)  in
                          FStar_SMTEncoding_Term.mkForall uu____13252
                            uu____13253
                           in
                        (uu____13251,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13243  in
                    [uu____13242]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13239
                   in
                let uu____13308 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13308, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13311,uu____13312) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13322  ->
                   match uu___4_13322 with
                   | FStar_Syntax_Syntax.Discriminator uu____13324 -> true
                   | uu____13326 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13328,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13340 =
                      let uu____13342 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13342.FStar_Ident.idText  in
                    uu____13340 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13349  ->
                      match uu___5_13349 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13352 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13355) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13369  ->
                   match uu___6_13369 with
                   | FStar_Syntax_Syntax.Projector uu____13371 -> true
                   | uu____13377 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13381 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13381 with
            | FStar_Pervasives_Native.Some uu____13388 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1055_13390 = se  in
                  let uu____13391 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13391;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1055_13390.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1055_13390.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1055_13390.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13394) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13409) ->
           let uu____13418 = encode_sigelts env ses  in
           (match uu____13418 with
            | (g,env1) ->
                let uu____13429 =
                  FStar_List.fold_left
                    (fun uu____13453  ->
                       fun elt  ->
                         match uu____13453 with
                         | (g',inversions) ->
                             let uu____13481 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_13504  ->
                                       match uu___7_13504 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13506;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13507;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13508;_}
                                           -> false
                                       | uu____13515 -> true))
                                in
                             (match uu____13481 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1087_13540 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1087_13540.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1087_13540.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1087_13540.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13429 with
                 | (g',inversions) ->
                     let uu____13559 =
                       FStar_List.fold_left
                         (fun uu____13590  ->
                            fun elt  ->
                              match uu____13590 with
                              | (decls,elts,rest) ->
                                  let uu____13631 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_13640  ->
                                            match uu___8_13640 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____13642 -> true
                                            | uu____13655 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____13631
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____13678 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_13699  ->
                                               match uu___9_13699 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____13701 -> true
                                               | uu____13714 -> false))
                                        in
                                     match uu____13678 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1109_13745 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1109_13745.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1109_13745.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1109_13745.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____13559 with
                      | (decls,elts,rest) ->
                          let uu____13771 =
                            let uu____13772 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____13779 =
                              let uu____13782 =
                                let uu____13785 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____13785  in
                              FStar_List.append elts uu____13782  in
                            FStar_List.append uu____13772 uu____13779  in
                          (uu____13771, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____13796,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____13809 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____13809 with
             | (usubst,uvs) ->
                 let uu____13829 =
                   let uu____13836 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____13837 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____13838 =
                     let uu____13839 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____13839 k  in
                   (uu____13836, uu____13837, uu____13838)  in
                 (match uu____13829 with
                  | (env1,tps1,k1) ->
                      let uu____13852 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____13852 with
                       | (tps2,k2) ->
                           let uu____13860 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____13860 with
                            | (uu____13876,k3) ->
                                let uu____13898 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____13898 with
                                 | (tps3,env_tps,uu____13910,us) ->
                                     let u_k =
                                       let uu____13913 =
                                         let uu____13914 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____13915 =
                                           let uu____13920 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____13922 =
                                             let uu____13923 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____13923
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____13920 uu____13922
                                            in
                                         uu____13915
                                           FStar_Pervasives_Native.None
                                           uu____13914
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____13913 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____13941) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____13947,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____13950) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____13958,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____13965) ->
                                           let uu____13966 =
                                             let uu____13968 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13968
                                              in
                                           failwith uu____13966
                                       | (uu____13972,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____13973 =
                                             let uu____13975 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13975
                                              in
                                           failwith uu____13973
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____13979,uu____13980) ->
                                           let uu____13989 =
                                             let uu____13991 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13991
                                              in
                                           failwith uu____13989
                                       | (uu____13995,FStar_Syntax_Syntax.U_unif
                                          uu____13996) ->
                                           let uu____14005 =
                                             let uu____14007 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14007
                                              in
                                           failwith uu____14005
                                       | uu____14011 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14024 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14024 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14042 = u_leq_u_k u_tp  in
                                       if uu____14042
                                       then true
                                       else
                                         (let uu____14049 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14049 with
                                          | (formals,uu____14066) ->
                                              let uu____14087 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14087 with
                                               | (uu____14097,uu____14098,uu____14099,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14110 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14110
             then
               let uu____14115 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14115
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14135  ->
                       match uu___10_14135 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14139 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14152 = c  in
                 match uu____14152 with
                 | (name,args,uu____14157,uu____14158,uu____14159) ->
                     let uu____14170 =
                       let uu____14171 =
                         let uu____14183 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14210  ->
                                   match uu____14210 with
                                   | (uu____14219,sort,uu____14221) -> sort))
                            in
                         (name, uu____14183,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14171  in
                     [uu____14170]
               else
                 (let uu____14232 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14232 c)
                in
             let inversion_axioms tapp vars =
               let uu____14250 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14258 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14258 FStar_Option.isNone))
                  in
               if uu____14250
               then []
               else
                 (let uu____14293 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14293 with
                  | (xxsym,xx) ->
                      let uu____14306 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14345  ->
                                fun l  ->
                                  match uu____14345 with
                                  | (out,decls) ->
                                      let uu____14365 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14365 with
                                       | (uu____14376,data_t) ->
                                           let uu____14378 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14378 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14422 =
                                                    let uu____14423 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14423.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14422 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14426,indices)
                                                      -> indices
                                                  | uu____14452 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14482  ->
                                                            match uu____14482
                                                            with
                                                            | (x,uu____14490)
                                                                ->
                                                                let uu____14495
                                                                  =
                                                                  let uu____14496
                                                                    =
                                                                    let uu____14504
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14504,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14496
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14495)
                                                       env)
                                                   in
                                                let uu____14509 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14509 with
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
                                                                  let uu____14544
                                                                    =
                                                                    let uu____14549
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____14549,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____14544)
                                                             vars indices1
                                                         else []  in
                                                       let uu____14552 =
                                                         let uu____14553 =
                                                           let uu____14558 =
                                                             let uu____14559
                                                               =
                                                               let uu____14564
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____14565
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____14564,
                                                                 uu____14565)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____14559
                                                              in
                                                           (out, uu____14558)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____14553
                                                          in
                                                       (uu____14552,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14306 with
                       | (data_ax,decls) ->
                           let uu____14580 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____14580 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____14597 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____14597 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____14604 =
                                    let uu____14612 =
                                      let uu____14613 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____14614 =
                                        let uu____14625 =
                                          let uu____14626 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____14628 =
                                            let uu____14631 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____14631 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____14626 uu____14628
                                           in
                                        let uu____14633 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____14625,
                                          uu____14633)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____14613 uu____14614
                                       in
                                    let uu____14642 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____14612,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____14642)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____14604
                                   in
                                let uu____14648 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____14648)))
                in
             let uu____14655 =
               let uu____14660 =
                 let uu____14661 = FStar_Syntax_Subst.compress k  in
                 uu____14661.FStar_Syntax_Syntax.n  in
               match uu____14660 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____14696 -> (tps, k)  in
             match uu____14655 with
             | (formals,res) ->
                 let uu____14703 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____14703 with
                  | (formals1,res1) ->
                      let uu____14714 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____14714 with
                       | (vars,guards,env',binder_decls,uu____14739) ->
                           let arity = FStar_List.length vars  in
                           let uu____14753 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____14753 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____14779 =
                                    let uu____14787 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____14787)  in
                                  FStar_SMTEncoding_Util.mkApp uu____14779
                                   in
                                let uu____14793 =
                                  let tname_decl =
                                    let uu____14803 =
                                      let uu____14804 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____14823 =
                                                  let uu____14825 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____14825
                                                   in
                                                let uu____14827 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____14823, uu____14827,
                                                  false)))
                                         in
                                      let uu____14831 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____14804,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____14831, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____14803
                                     in
                                  let uu____14839 =
                                    match vars with
                                    | [] ->
                                        let uu____14852 =
                                          let uu____14853 =
                                            let uu____14856 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _14862  ->
                                                 FStar_Pervasives_Native.Some
                                                   _14862) uu____14856
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____14853
                                           in
                                        ([], uu____14852)
                                    | uu____14865 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____14875 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____14875
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____14891 =
                                            let uu____14899 =
                                              let uu____14900 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____14901 =
                                                let uu____14917 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____14917)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____14900 uu____14901
                                               in
                                            (uu____14899,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____14891
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____14839 with
                                  | (tok_decls,env2) ->
                                      let uu____14944 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____14944
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____14793 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____14972 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____14972 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____14994 =
                                                 let uu____14995 =
                                                   let uu____15003 =
                                                     let uu____15004 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____15004
                                                      in
                                                   (uu____15003,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____14995
                                                  in
                                               [uu____14994]
                                             else []  in
                                           let uu____15012 =
                                             let uu____15015 =
                                               let uu____15018 =
                                                 let uu____15021 =
                                                   let uu____15022 =
                                                     let uu____15030 =
                                                       let uu____15031 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____15032 =
                                                         let uu____15043 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____15043)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____15031
                                                         uu____15032
                                                        in
                                                     (uu____15030,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____15022
                                                    in
                                                 [uu____15021]  in
                                               FStar_List.append karr
                                                 uu____15018
                                                in
                                             FStar_All.pipe_right uu____15015
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____15012
                                        in
                                     let aux =
                                       let uu____15062 =
                                         let uu____15065 =
                                           inversion_axioms tapp vars  in
                                         let uu____15068 =
                                           let uu____15071 =
                                             let uu____15074 =
                                               let uu____15075 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____15075 env2
                                                 tapp vars
                                                in
                                             [uu____15074]  in
                                           FStar_All.pipe_right uu____15071
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____15065
                                           uu____15068
                                          in
                                       FStar_List.append kindingAx
                                         uu____15062
                                        in
                                     let g =
                                       let uu____15083 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____15083
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15091,uu____15092,uu____15093,uu____15094,uu____15095)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15103,t,uu____15105,n_tps,uu____15107) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____15117 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____15117 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15165 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15165 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15189 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15189 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15209 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15209 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15288 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15288,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15295 =
                                   let uu____15296 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15296, true)
                                    in
                                 let uu____15304 =
                                   let uu____15311 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15311
                                    in
                                 FStar_All.pipe_right uu____15295 uu____15304
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
                               let uu____15323 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____15323 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15335::uu____15336 ->
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
                                            let uu____15385 =
                                              let uu____15386 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15386]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15385
                                             in
                                          let uu____15412 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15413 =
                                            let uu____15424 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15424)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15412 uu____15413
                                      | uu____15451 -> tok_typing  in
                                    let uu____15462 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15462 with
                                     | (vars',guards',env'',decls_formals,uu____15487)
                                         ->
                                         let uu____15500 =
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
                                         (match uu____15500 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____15530 ->
                                                    let uu____15539 =
                                                      let uu____15540 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____15540
                                                       in
                                                    [uu____15539]
                                                 in
                                              let encode_elim uu____15556 =
                                                let uu____15557 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____15557 with
                                                | (head1,args) ->
                                                    let uu____15608 =
                                                      let uu____15609 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____15609.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____15608 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____15621;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____15622;_},uu____15623)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____15629 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____15629
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
                                                                  | uu____15692
                                                                    ->
                                                                    let uu____15693
                                                                    =
                                                                    let uu____15699
                                                                    =
                                                                    let uu____15701
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15701
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15699)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15693
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15724
                                                                    =
                                                                    let uu____15726
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15726
                                                                     in
                                                                    if
                                                                    uu____15724
                                                                    then
                                                                    let uu____15748
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15748]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____15751
                                                                =
                                                                let uu____15765
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____15822
                                                                     ->
                                                                    fun
                                                                    uu____15823
                                                                     ->
                                                                    match 
                                                                    (uu____15822,
                                                                    uu____15823)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15934
                                                                    =
                                                                    let uu____15942
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15942
                                                                     in
                                                                    (match uu____15934
                                                                    with
                                                                    | 
                                                                    (uu____15956,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15967
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15967
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15972
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15972
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
                                                                  uu____15765
                                                                 in
                                                              (match uu____15751
                                                               with
                                                               | (uu____15993,arg_vars,elim_eqns_or_guards,uu____15996)
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
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16047
                                                                    =
                                                                    let uu____16048
                                                                    =
                                                                    let uu____16053
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16053)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16048
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16044,
                                                                    uu____16047)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16032
                                                                    uu____16033
                                                                     in
                                                                    (uu____16031,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16023
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16068
                                                                    =
                                                                    let uu____16069
                                                                    =
                                                                    let uu____16075
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16075,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16069
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16068
                                                                     in
                                                                    let uu____16078
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16078
                                                                    then
                                                                    let x =
                                                                    let uu____16082
                                                                    =
                                                                    let uu____16088
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16088,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16082
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16093
                                                                    =
                                                                    let uu____16101
                                                                    =
                                                                    let uu____16102
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16103
                                                                    =
                                                                    let uu____16114
                                                                    =
                                                                    let uu____16119
                                                                    =
                                                                    let uu____16122
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16122]
                                                                     in
                                                                    [uu____16119]
                                                                     in
                                                                    let uu____16127
                                                                    =
                                                                    let uu____16128
                                                                    =
                                                                    let uu____16133
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16135
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16133,
                                                                    uu____16135)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16128
                                                                     in
                                                                    (uu____16114,
                                                                    [x],
                                                                    uu____16127)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16102
                                                                    uu____16103
                                                                     in
                                                                    let uu____16156
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16101,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16156)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16093
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16167
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
                                                                    (let uu____16190
                                                                    =
                                                                    let uu____16191
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16191
                                                                    dapp1  in
                                                                    [uu____16190])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16167
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16198
                                                                    =
                                                                    let uu____16206
                                                                    =
                                                                    let uu____16207
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16208
                                                                    =
                                                                    let uu____16219
                                                                    =
                                                                    let uu____16220
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16220
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16222
                                                                    =
                                                                    let uu____16223
                                                                    =
                                                                    let uu____16228
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16228)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16223
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16219,
                                                                    uu____16222)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16207
                                                                    uu____16208
                                                                     in
                                                                    (uu____16206,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16198)
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
                                                         let uu____16247 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16247
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
                                                                  | uu____16310
                                                                    ->
                                                                    let uu____16311
                                                                    =
                                                                    let uu____16317
                                                                    =
                                                                    let uu____16319
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16319
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16317)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16311
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16342
                                                                    =
                                                                    let uu____16344
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16344
                                                                     in
                                                                    if
                                                                    uu____16342
                                                                    then
                                                                    let uu____16366
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16366]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16369
                                                                =
                                                                let uu____16383
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16440
                                                                     ->
                                                                    fun
                                                                    uu____16441
                                                                     ->
                                                                    match 
                                                                    (uu____16440,
                                                                    uu____16441)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16552
                                                                    =
                                                                    let uu____16560
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16560
                                                                     in
                                                                    (match uu____16552
                                                                    with
                                                                    | 
                                                                    (uu____16574,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16585
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16585
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16590
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16590
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
                                                                  uu____16383
                                                                 in
                                                              (match uu____16369
                                                               with
                                                               | (uu____16611,arg_vars,elim_eqns_or_guards,uu____16614)
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
                                                                    let uu____16641
                                                                    =
                                                                    let uu____16649
                                                                    =
                                                                    let uu____16650
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16651
                                                                    =
                                                                    let uu____16662
                                                                    =
                                                                    let uu____16663
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16663
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16665
                                                                    =
                                                                    let uu____16666
                                                                    =
                                                                    let uu____16671
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16671)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16666
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16662,
                                                                    uu____16665)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16650
                                                                    uu____16651
                                                                     in
                                                                    (uu____16649,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16641
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16686
                                                                    =
                                                                    let uu____16687
                                                                    =
                                                                    let uu____16693
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16693,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16687
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16686
                                                                     in
                                                                    let uu____16696
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16696
                                                                    then
                                                                    let x =
                                                                    let uu____16700
                                                                    =
                                                                    let uu____16706
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16706,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16700
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16711
                                                                    =
                                                                    let uu____16719
                                                                    =
                                                                    let uu____16720
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16721
                                                                    =
                                                                    let uu____16732
                                                                    =
                                                                    let uu____16737
                                                                    =
                                                                    let uu____16740
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16740]
                                                                     in
                                                                    [uu____16737]
                                                                     in
                                                                    let uu____16745
                                                                    =
                                                                    let uu____16746
                                                                    =
                                                                    let uu____16751
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16753
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16751,
                                                                    uu____16753)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16746
                                                                     in
                                                                    (uu____16732,
                                                                    [x],
                                                                    uu____16745)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16720
                                                                    uu____16721
                                                                     in
                                                                    let uu____16774
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16719,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16774)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16711
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16785
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
                                                                    (let uu____16808
                                                                    =
                                                                    let uu____16809
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16809
                                                                    dapp1  in
                                                                    [uu____16808])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16785
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16816
                                                                    =
                                                                    let uu____16824
                                                                    =
                                                                    let uu____16825
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16826
                                                                    =
                                                                    let uu____16837
                                                                    =
                                                                    let uu____16838
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16838
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16840
                                                                    =
                                                                    let uu____16841
                                                                    =
                                                                    let uu____16846
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16846)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16841
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16837,
                                                                    uu____16840)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16825
                                                                    uu____16826
                                                                     in
                                                                    (uu____16824,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16816)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____16863 ->
                                                         ((let uu____16865 =
                                                             let uu____16871
                                                               =
                                                               let uu____16873
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____16875
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____16873
                                                                 uu____16875
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____16871)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____16865);
                                                          ([], [])))
                                                 in
                                              let uu____16883 =
                                                encode_elim ()  in
                                              (match uu____16883 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____16909 =
                                                       let uu____16912 =
                                                         let uu____16915 =
                                                           let uu____16918 =
                                                             let uu____16921
                                                               =
                                                               let uu____16924
                                                                 =
                                                                 let uu____16927
                                                                   =
                                                                   let uu____16928
                                                                    =
                                                                    let uu____16940
                                                                    =
                                                                    let uu____16941
                                                                    =
                                                                    let uu____16943
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16943
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____16941
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____16940)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____16928
                                                                    in
                                                                 [uu____16927]
                                                                  in
                                                               FStar_List.append
                                                                 uu____16924
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____16921
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____16954 =
                                                             let uu____16957
                                                               =
                                                               let uu____16960
                                                                 =
                                                                 let uu____16963
                                                                   =
                                                                   let uu____16966
                                                                    =
                                                                    let uu____16969
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____16974
                                                                    =
                                                                    let uu____16977
                                                                    =
                                                                    let uu____16978
                                                                    =
                                                                    let uu____16986
                                                                    =
                                                                    let uu____16987
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16988
                                                                    =
                                                                    let uu____16999
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16999)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16987
                                                                    uu____16988
                                                                     in
                                                                    (uu____16986,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16978
                                                                     in
                                                                    let uu____17012
                                                                    =
                                                                    let uu____17015
                                                                    =
                                                                    let uu____17016
                                                                    =
                                                                    let uu____17024
                                                                    =
                                                                    let uu____17025
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17026
                                                                    =
                                                                    let uu____17037
                                                                    =
                                                                    let uu____17038
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17038
                                                                    vars'  in
                                                                    let uu____17040
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17037,
                                                                    uu____17040)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17025
                                                                    uu____17026
                                                                     in
                                                                    (uu____17024,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17016
                                                                     in
                                                                    [uu____17015]
                                                                     in
                                                                    uu____16977
                                                                    ::
                                                                    uu____17012
                                                                     in
                                                                    uu____16969
                                                                    ::
                                                                    uu____16974
                                                                     in
                                                                   FStar_List.append
                                                                    uu____16966
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____16963
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____16960
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____16957
                                                              in
                                                           FStar_List.append
                                                             uu____16918
                                                             uu____16954
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____16915
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____16912
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____16909
                                                      in
                                                   let uu____17057 =
                                                     let uu____17058 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17058 g
                                                      in
                                                   (uu____17057, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17092  ->
              fun se  ->
                match uu____17092 with
                | (g,env1) ->
                    let uu____17112 = encode_sigelt env1 se  in
                    (match uu____17112 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17180 =
        match uu____17180 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17217 ->
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
                 ((let uu____17225 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17225
                   then
                     let uu____17230 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17232 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17234 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17230 uu____17232 uu____17234
                   else ());
                  (let uu____17239 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17239 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17257 =
                         let uu____17265 =
                           let uu____17267 =
                             let uu____17269 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17269
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17267  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17265
                          in
                       (match uu____17257 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17289 = FStar_Options.log_queries ()
                                 in
                              if uu____17289
                              then
                                let uu____17292 =
                                  let uu____17294 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17296 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17298 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17294 uu____17296 uu____17298
                                   in
                                FStar_Pervasives_Native.Some uu____17292
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17314 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17324 =
                                let uu____17327 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17327  in
                              FStar_List.append uu____17314 uu____17324  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17339,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17359 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17359 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____17380 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____17380 with | (uu____17407,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17460  ->
              match uu____17460 with
              | (l,uu____17469,uu____17470) ->
                  let uu____17473 =
                    let uu____17485 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17485, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17473))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17518  ->
              match uu____17518 with
              | (l,uu____17529,uu____17530) ->
                  let uu____17533 =
                    let uu____17534 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _17537  -> FStar_SMTEncoding_Term.Echo _17537)
                      uu____17534
                     in
                  let uu____17538 =
                    let uu____17541 =
                      let uu____17542 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17542  in
                    [uu____17541]  in
                  uu____17533 :: uu____17538))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17560 =
      let uu____17563 =
        let uu____17564 = FStar_Util.psmap_empty ()  in
        let uu____17579 =
          let uu____17588 = FStar_Util.psmap_empty ()  in (uu____17588, [])
           in
        let uu____17595 =
          let uu____17597 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____17597 FStar_Ident.string_of_lid  in
        let uu____17599 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17564;
          FStar_SMTEncoding_Env.fvar_bindings = uu____17579;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____17595;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____17599
        }  in
      [uu____17563]  in
    FStar_ST.op_Colon_Equals last_env uu____17560
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____17643 = FStar_ST.op_Bang last_env  in
      match uu____17643 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17671 ->
          let uu___1536_17674 = e  in
          let uu____17675 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1536_17674.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1536_17674.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1536_17674.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1536_17674.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1536_17674.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1536_17674.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1536_17674.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____17675;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1536_17674.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1536_17674.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____17683 = FStar_ST.op_Bang last_env  in
    match uu____17683 with
    | [] -> failwith "Empty env stack"
    | uu____17710::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____17742  ->
    let uu____17743 = FStar_ST.op_Bang last_env  in
    match uu____17743 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____17803  ->
    let uu____17804 = FStar_ST.op_Bang last_env  in
    match uu____17804 with
    | [] -> failwith "Popping an empty stack"
    | uu____17831::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____17868  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____17921  ->
         let uu____17922 = snapshot_env ()  in
         match uu____17922 with
         | (env_depth,()) ->
             let uu____17944 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____17944 with
              | (varops_depth,()) ->
                  let uu____17966 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____17966 with
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
        (fun uu____18024  ->
           let uu____18025 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18025 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18120 = snapshot msg  in () 
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
        | (uu____18166::uu____18167,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1597_18175 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1597_18175.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1597_18175.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1597_18175.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18176 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1603_18203 = elt  in
        let uu____18204 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1603_18203.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1603_18203.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18204;
          FStar_SMTEncoding_Term.a_names =
            (uu___1603_18203.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18224 =
        let uu____18227 =
          let uu____18228 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18228  in
        let uu____18229 = open_fact_db_tags env  in uu____18227 ::
          uu____18229
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18224
  
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
      let uu____18256 = encode_sigelt env se  in
      match uu____18256 with
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
                (let uu____18302 =
                   let uu____18305 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18305
                    in
                 match uu____18302 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18320 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18320
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18350 = FStar_Options.log_queries ()  in
        if uu____18350
        then
          let uu____18355 =
            let uu____18356 =
              let uu____18358 =
                let uu____18360 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18360 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18358  in
            FStar_SMTEncoding_Term.Caption uu____18356  in
          uu____18355 :: decls
        else decls  in
      (let uu____18379 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18379
       then
         let uu____18382 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18382
       else ());
      (let env =
         let uu____18388 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18388 tcenv  in
       let uu____18389 = encode_top_level_facts env se  in
       match uu____18389 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18403 =
               let uu____18406 =
                 let uu____18409 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18409
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18406  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18403)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18442 = FStar_Options.log_queries ()  in
          if uu____18442
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1641_18462 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1641_18462.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1641_18462.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1641_18462.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1641_18462.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1641_18462.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1641_18462.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1641_18462.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1641_18462.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1641_18462.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1641_18462.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18467 =
             let uu____18470 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18470
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18467  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18490 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18490
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
          (let uu____18514 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____18514
           then
             let uu____18517 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____18517
           else ());
          (let env =
             let uu____18525 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____18525
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____18564  ->
                     fun se  ->
                       match uu____18564 with
                       | (g,env2) ->
                           let uu____18584 = encode_top_level_facts env2 se
                              in
                           (match uu____18584 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____18607 =
             encode_signature
               (let uu___1664_18616 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1664_18616.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1664_18616.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1664_18616.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1664_18616.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1664_18616.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1664_18616.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1664_18616.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1664_18616.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1664_18616.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1664_18616.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____18607 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____18632 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18632
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____18638 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____18638))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____18666  ->
        match uu____18666 with
        | (decls,fvbs) ->
            ((let uu____18680 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____18680
              then ()
              else
                (let uu____18685 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18685
                 then
                   let uu____18688 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____18688
                 else ()));
             (let env =
                let uu____18696 = get_env name tcenv  in
                FStar_All.pipe_right uu____18696
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____18698 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____18698
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____18712 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____18712
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
        (let uu____18774 =
           let uu____18776 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____18776.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____18774);
        (let env =
           let uu____18778 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____18778 tcenv  in
         let uu____18779 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____18818 = aux rest  in
                 (match uu____18818 with
                  | (out,rest1) ->
                      let t =
                        let uu____18846 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____18846 with
                        | FStar_Pervasives_Native.Some uu____18849 ->
                            let uu____18850 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____18850
                              x.FStar_Syntax_Syntax.sort
                        | uu____18851 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____18855 =
                        let uu____18858 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1705_18861 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1705_18861.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1705_18861.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____18858 :: out  in
                      (uu____18855, rest1))
             | uu____18866 -> ([], bindings)  in
           let uu____18873 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____18873 with
           | (closing,bindings) ->
               let uu____18900 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____18900, bindings)
            in
         match uu____18779 with
         | (q1,bindings) ->
             let uu____18931 = encode_env_bindings env bindings  in
             (match uu____18931 with
              | (env_decls,env1) ->
                  ((let uu____18953 =
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
                    if uu____18953
                    then
                      let uu____18960 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____18960
                    else ());
                   (let uu____18965 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____18965 with
                    | (phi,qdecls) ->
                        let uu____18986 =
                          let uu____18991 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____18991 phi
                           in
                        (match uu____18986 with
                         | (labels,phi1) ->
                             let uu____19008 = encode_labels labels  in
                             (match uu____19008 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19044 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19044
                                    then
                                      let uu____19049 =
                                        let uu____19050 =
                                          let uu____19052 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____19052
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19050
                                         in
                                      [uu____19049]
                                    else []  in
                                  let query_prelude =
                                    let uu____19060 =
                                      let uu____19061 =
                                        let uu____19062 =
                                          let uu____19065 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19072 =
                                            let uu____19075 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19075
                                             in
                                          FStar_List.append uu____19065
                                            uu____19072
                                           in
                                        FStar_List.append env_decls
                                          uu____19062
                                         in
                                      FStar_All.pipe_right uu____19061
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19060
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19085 =
                                      let uu____19093 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19094 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19093,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19094)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19085
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
  