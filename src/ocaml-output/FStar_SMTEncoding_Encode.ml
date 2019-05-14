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
  let uu____155 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____155 with
  | (asym,a) ->
      let uu____166 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____166 with
       | (xsym,x) ->
           let uu____177 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____177 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____255 =
                      let uu____267 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____267, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____255  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____287 =
                      let uu____295 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____295)  in
                    FStar_SMTEncoding_Util.mkApp uu____287  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____314 =
                    let uu____317 =
                      let uu____320 =
                        let uu____323 =
                          let uu____324 =
                            let uu____332 =
                              let uu____333 =
                                let uu____344 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____344)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____333
                               in
                            (uu____332, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____324  in
                        let uu____356 =
                          let uu____359 =
                            let uu____360 =
                              let uu____368 =
                                let uu____369 =
                                  let uu____380 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____380)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____369
                                 in
                              (uu____368,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____360  in
                          [uu____359]  in
                        uu____323 :: uu____356  in
                      xtok_decl :: uu____320  in
                    xname_decl :: uu____317  in
                  (xtok1, (FStar_List.length vars), uu____314)  in
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
                  let uu____550 =
                    let uu____571 =
                      let uu____590 =
                        let uu____591 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____591
                         in
                      quant axy uu____590  in
                    (FStar_Parser_Const.op_Eq, uu____571)  in
                  let uu____608 =
                    let uu____631 =
                      let uu____652 =
                        let uu____671 =
                          let uu____672 =
                            let uu____673 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____673  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____672
                           in
                        quant axy uu____671  in
                      (FStar_Parser_Const.op_notEq, uu____652)  in
                    let uu____690 =
                      let uu____713 =
                        let uu____734 =
                          let uu____753 =
                            let uu____754 =
                              let uu____755 =
                                let uu____760 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____761 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____760, uu____761)  in
                              FStar_SMTEncoding_Util.mkAnd uu____755  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____754
                             in
                          quant xy uu____753  in
                        (FStar_Parser_Const.op_And, uu____734)  in
                      let uu____778 =
                        let uu____801 =
                          let uu____822 =
                            let uu____841 =
                              let uu____842 =
                                let uu____843 =
                                  let uu____848 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____849 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____848, uu____849)  in
                                FStar_SMTEncoding_Util.mkOr uu____843  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____842
                               in
                            quant xy uu____841  in
                          (FStar_Parser_Const.op_Or, uu____822)  in
                        let uu____866 =
                          let uu____889 =
                            let uu____910 =
                              let uu____929 =
                                let uu____930 =
                                  let uu____931 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____931  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____930
                                 in
                              quant qx uu____929  in
                            (FStar_Parser_Const.op_Negation, uu____910)  in
                          let uu____948 =
                            let uu____971 =
                              let uu____992 =
                                let uu____1011 =
                                  let uu____1012 =
                                    let uu____1013 =
                                      let uu____1018 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1019 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1018, uu____1019)  in
                                    FStar_SMTEncoding_Util.mkLT uu____1013
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1012
                                   in
                                quant xy uu____1011  in
                              (FStar_Parser_Const.op_LT, uu____992)  in
                            let uu____1036 =
                              let uu____1059 =
                                let uu____1080 =
                                  let uu____1099 =
                                    let uu____1100 =
                                      let uu____1101 =
                                        let uu____1106 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1107 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1106, uu____1107)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1101
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1100
                                     in
                                  quant xy uu____1099  in
                                (FStar_Parser_Const.op_LTE, uu____1080)  in
                              let uu____1124 =
                                let uu____1147 =
                                  let uu____1168 =
                                    let uu____1187 =
                                      let uu____1188 =
                                        let uu____1189 =
                                          let uu____1194 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1195 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1194, uu____1195)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1189
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1188
                                       in
                                    quant xy uu____1187  in
                                  (FStar_Parser_Const.op_GT, uu____1168)  in
                                let uu____1212 =
                                  let uu____1235 =
                                    let uu____1256 =
                                      let uu____1275 =
                                        let uu____1276 =
                                          let uu____1277 =
                                            let uu____1282 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1283 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1282, uu____1283)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1277
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1276
                                         in
                                      quant xy uu____1275  in
                                    (FStar_Parser_Const.op_GTE, uu____1256)
                                     in
                                  let uu____1300 =
                                    let uu____1323 =
                                      let uu____1344 =
                                        let uu____1363 =
                                          let uu____1364 =
                                            let uu____1365 =
                                              let uu____1370 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1371 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1370, uu____1371)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1365
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1364
                                           in
                                        quant xy uu____1363  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1344)
                                       in
                                    let uu____1388 =
                                      let uu____1411 =
                                        let uu____1432 =
                                          let uu____1451 =
                                            let uu____1452 =
                                              let uu____1453 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1453
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1452
                                             in
                                          quant qx uu____1451  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1432)
                                         in
                                      let uu____1470 =
                                        let uu____1493 =
                                          let uu____1514 =
                                            let uu____1533 =
                                              let uu____1534 =
                                                let uu____1535 =
                                                  let uu____1540 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1541 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1540, uu____1541)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1535
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1534
                                               in
                                            quant xy uu____1533  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1514)
                                           in
                                        let uu____1558 =
                                          let uu____1581 =
                                            let uu____1602 =
                                              let uu____1621 =
                                                let uu____1622 =
                                                  let uu____1623 =
                                                    let uu____1628 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____1629 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____1628, uu____1629)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____1623
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____1622
                                                 in
                                              quant xy uu____1621  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____1602)
                                             in
                                          let uu____1646 =
                                            let uu____1669 =
                                              let uu____1690 =
                                                let uu____1709 =
                                                  let uu____1710 =
                                                    let uu____1711 =
                                                      let uu____1716 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____1717 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____1716,
                                                        uu____1717)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____1711
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____1710
                                                   in
                                                quant xy uu____1709  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____1690)
                                               in
                                            let uu____1734 =
                                              let uu____1757 =
                                                let uu____1778 =
                                                  let uu____1797 =
                                                    let uu____1798 =
                                                      let uu____1799 =
                                                        let uu____1804 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____1805 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____1804,
                                                          uu____1805)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____1799
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____1798
                                                     in
                                                  quant xy uu____1797  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____1778)
                                                 in
                                              let uu____1822 =
                                                let uu____1845 =
                                                  let uu____1866 =
                                                    let uu____1885 =
                                                      let uu____1886 =
                                                        let uu____1887 =
                                                          let uu____1892 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____1893 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____1892,
                                                            uu____1893)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____1887
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____1886
                                                       in
                                                    quant xy uu____1885  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____1866)
                                                   in
                                                let uu____1910 =
                                                  let uu____1933 =
                                                    let uu____1954 =
                                                      let uu____1973 =
                                                        let uu____1974 =
                                                          let uu____1975 =
                                                            let uu____1980 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____1981 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____1980,
                                                              uu____1981)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____1975
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____1974
                                                         in
                                                      quant xy uu____1973  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____1954)
                                                     in
                                                  let uu____1998 =
                                                    let uu____2021 =
                                                      let uu____2042 =
                                                        let uu____2061 =
                                                          let uu____2062 =
                                                            let uu____2063 =
                                                              let uu____2068
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2069
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2068,
                                                                uu____2069)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2063
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2062
                                                           in
                                                        quant xy uu____2061
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2042)
                                                       in
                                                    let uu____2086 =
                                                      let uu____2109 =
                                                        let uu____2130 =
                                                          let uu____2149 =
                                                            let uu____2150 =
                                                              let uu____2151
                                                                =
                                                                let uu____2156
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2157
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2156,
                                                                  uu____2157)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2151
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2150
                                                             in
                                                          quant xy uu____2149
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2130)
                                                         in
                                                      let uu____2174 =
                                                        let uu____2197 =
                                                          let uu____2218 =
                                                            let uu____2237 =
                                                              let uu____2238
                                                                =
                                                                let uu____2239
                                                                  =
                                                                  let uu____2244
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2245
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2244,
                                                                    uu____2245)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2239
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2238
                                                               in
                                                            quant xy
                                                              uu____2237
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2218)
                                                           in
                                                        let uu____2262 =
                                                          let uu____2285 =
                                                            let uu____2306 =
                                                              let uu____2325
                                                                =
                                                                let uu____2326
                                                                  =
                                                                  let uu____2327
                                                                    =
                                                                    let uu____2332
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2333
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2332,
                                                                    uu____2333)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2327
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2326
                                                                 in
                                                              quant xy
                                                                uu____2325
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2306)
                                                             in
                                                          let uu____2350 =
                                                            let uu____2373 =
                                                              let uu____2394
                                                                =
                                                                let uu____2413
                                                                  =
                                                                  let uu____2414
                                                                    =
                                                                    let uu____2415
                                                                    =
                                                                    let uu____2420
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2421
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2420,
                                                                    uu____2421)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2415
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2414
                                                                   in
                                                                quant xy
                                                                  uu____2413
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2394)
                                                               in
                                                            let uu____2438 =
                                                              let uu____2461
                                                                =
                                                                let uu____2482
                                                                  =
                                                                  let uu____2501
                                                                    =
                                                                    let uu____2502
                                                                    =
                                                                    let uu____2503
                                                                    =
                                                                    let uu____2508
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2509
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2508,
                                                                    uu____2509)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2503
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2502
                                                                     in
                                                                  quant xy
                                                                    uu____2501
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2482)
                                                                 in
                                                              let uu____2526
                                                                =
                                                                let uu____2549
                                                                  =
                                                                  let uu____2570
                                                                    =
                                                                    let uu____2589
                                                                    =
                                                                    let uu____2590
                                                                    =
                                                                    let uu____2591
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____2591
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2590
                                                                     in
                                                                    quant qx
                                                                    uu____2589
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____2570)
                                                                   in
                                                                [uu____2549]
                                                                 in
                                                              uu____2461 ::
                                                                uu____2526
                                                               in
                                                            uu____2373 ::
                                                              uu____2438
                                                             in
                                                          uu____2285 ::
                                                            uu____2350
                                                           in
                                                        uu____2197 ::
                                                          uu____2262
                                                         in
                                                      uu____2109 ::
                                                        uu____2174
                                                       in
                                                    uu____2021 :: uu____2086
                                                     in
                                                  uu____1933 :: uu____1998
                                                   in
                                                uu____1845 :: uu____1910  in
                                              uu____1757 :: uu____1822  in
                                            uu____1669 :: uu____1734  in
                                          uu____1581 :: uu____1646  in
                                        uu____1493 :: uu____1558  in
                                      uu____1411 :: uu____1470  in
                                    uu____1323 :: uu____1388  in
                                  uu____1235 :: uu____1300  in
                                uu____1147 :: uu____1212  in
                              uu____1059 :: uu____1124  in
                            uu____971 :: uu____1036  in
                          uu____889 :: uu____948  in
                        uu____801 :: uu____866  in
                      uu____713 :: uu____778  in
                    uu____631 :: uu____690  in
                  uu____550 :: uu____608  in
                let mk1 l v1 =
                  let uu____3130 =
                    let uu____3142 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____3232  ->
                              match uu____3232 with
                              | (l',uu____3253) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3142
                      (FStar_Option.map
                         (fun uu____3352  ->
                            match uu____3352 with
                            | (uu____3380,b) ->
                                let uu____3414 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3414 v1))
                     in
                  FStar_All.pipe_right uu____3130 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____3497  ->
                          match uu____3497 with
                          | (l',uu____3518) -> FStar_Ident.lid_equals l l'))
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
          let uu____3592 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3592 with
          | (xxsym,xx) ->
              let uu____3603 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____3603 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____3619 =
                     let uu____3627 =
                       let uu____3628 =
                         let uu____3639 =
                           let uu____3640 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____3650 =
                             let uu____3661 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____3661 :: vars  in
                           uu____3640 :: uu____3650  in
                         let uu____3687 =
                           let uu____3688 =
                             let uu____3693 =
                               let uu____3694 =
                                 let uu____3699 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3699)  in
                               FStar_SMTEncoding_Util.mkEq uu____3694  in
                             (xx_has_type, uu____3693)  in
                           FStar_SMTEncoding_Util.mkImp uu____3688  in
                         ([[xx_has_type]], uu____3639, uu____3687)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____3628  in
                     let uu____3712 =
                       let uu____3714 =
                         let uu____3716 =
                           let uu____3718 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____3718  in
                         Prims.op_Hat module_name uu____3716  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3714
                        in
                     (uu____3627, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3712)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____3619)
  
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
    let uu____3774 =
      let uu____3776 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____3776  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3774  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3798 =
      let uu____3799 =
        let uu____3807 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3807, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3799  in
    let uu____3812 =
      let uu____3815 =
        let uu____3816 =
          let uu____3824 =
            let uu____3825 =
              let uu____3836 =
                let uu____3837 =
                  let uu____3842 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3842)  in
                FStar_SMTEncoding_Util.mkImp uu____3837  in
              ([[typing_pred]], [xx], uu____3836)  in
            let uu____3867 =
              let uu____3882 = FStar_TypeChecker_Env.get_range env  in
              let uu____3883 = mkForall_fuel1 env  in uu____3883 uu____3882
               in
            uu____3867 uu____3825  in
          (uu____3824, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3816  in
      [uu____3815]  in
    uu____3798 :: uu____3812  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3930 =
      let uu____3931 =
        let uu____3939 =
          let uu____3940 = FStar_TypeChecker_Env.get_range env  in
          let uu____3941 =
            let uu____3952 =
              let uu____3957 =
                let uu____3960 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3960]  in
              [uu____3957]  in
            let uu____3965 =
              let uu____3966 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3966 tt  in
            (uu____3952, [bb], uu____3965)  in
          FStar_SMTEncoding_Term.mkForall uu____3940 uu____3941  in
        (uu____3939, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3931  in
    let uu____3991 =
      let uu____3994 =
        let uu____3995 =
          let uu____4003 =
            let uu____4004 =
              let uu____4015 =
                let uu____4016 =
                  let uu____4021 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____4021)  in
                FStar_SMTEncoding_Util.mkImp uu____4016  in
              ([[typing_pred]], [xx], uu____4015)  in
            let uu____4048 =
              let uu____4063 = FStar_TypeChecker_Env.get_range env  in
              let uu____4064 = mkForall_fuel1 env  in uu____4064 uu____4063
               in
            uu____4048 uu____4004  in
          (uu____4003, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3995  in
      [uu____3994]  in
    uu____3930 :: uu____3991  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____4107 =
        let uu____4108 =
          let uu____4114 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4114, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4108  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4107  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4128 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4128  in
    let uu____4133 =
      let uu____4134 =
        let uu____4142 =
          let uu____4143 = FStar_TypeChecker_Env.get_range env  in
          let uu____4144 =
            let uu____4155 =
              let uu____4160 =
                let uu____4163 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4163]  in
              [uu____4160]  in
            let uu____4168 =
              let uu____4169 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4169 tt  in
            (uu____4155, [bb], uu____4168)  in
          FStar_SMTEncoding_Term.mkForall uu____4143 uu____4144  in
        (uu____4142, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4134  in
    let uu____4194 =
      let uu____4197 =
        let uu____4198 =
          let uu____4206 =
            let uu____4207 =
              let uu____4218 =
                let uu____4219 =
                  let uu____4224 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4224)  in
                FStar_SMTEncoding_Util.mkImp uu____4219  in
              ([[typing_pred]], [xx], uu____4218)  in
            let uu____4251 =
              let uu____4266 = FStar_TypeChecker_Env.get_range env  in
              let uu____4267 = mkForall_fuel1 env  in uu____4267 uu____4266
               in
            uu____4251 uu____4207  in
          (uu____4206, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4198  in
      let uu____4289 =
        let uu____4292 =
          let uu____4293 =
            let uu____4301 =
              let uu____4302 =
                let uu____4313 =
                  let uu____4314 =
                    let uu____4319 =
                      let uu____4320 =
                        let uu____4323 =
                          let uu____4326 =
                            let uu____4329 =
                              let uu____4330 =
                                let uu____4335 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4336 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____4335, uu____4336)  in
                              FStar_SMTEncoding_Util.mkGT uu____4330  in
                            let uu____4338 =
                              let uu____4341 =
                                let uu____4342 =
                                  let uu____4347 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4348 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____4347, uu____4348)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4342  in
                              let uu____4350 =
                                let uu____4353 =
                                  let uu____4354 =
                                    let uu____4359 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4360 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4359, uu____4360)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4354  in
                                [uu____4353]  in
                              uu____4341 :: uu____4350  in
                            uu____4329 :: uu____4338  in
                          typing_pred_y :: uu____4326  in
                        typing_pred :: uu____4323  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4320  in
                    (uu____4319, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4314  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4313)
                 in
              let uu____4393 =
                let uu____4408 = FStar_TypeChecker_Env.get_range env  in
                let uu____4409 = mkForall_fuel1 env  in uu____4409 uu____4408
                 in
              uu____4393 uu____4302  in
            (uu____4301,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4293  in
        [uu____4292]  in
      uu____4197 :: uu____4289  in
    uu____4133 :: uu____4194  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____4452 =
        let uu____4453 =
          let uu____4459 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4459, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4453  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4452  in
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
      let uu____4475 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4475  in
    let uu____4480 =
      let uu____4481 =
        let uu____4489 =
          let uu____4490 = FStar_TypeChecker_Env.get_range env  in
          let uu____4491 =
            let uu____4502 =
              let uu____4507 =
                let uu____4510 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4510]  in
              [uu____4507]  in
            let uu____4515 =
              let uu____4516 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4516 tt  in
            (uu____4502, [bb], uu____4515)  in
          FStar_SMTEncoding_Term.mkForall uu____4490 uu____4491  in
        (uu____4489, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4481  in
    let uu____4541 =
      let uu____4544 =
        let uu____4545 =
          let uu____4553 =
            let uu____4554 =
              let uu____4565 =
                let uu____4566 =
                  let uu____4571 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____4571)  in
                FStar_SMTEncoding_Util.mkImp uu____4566  in
              ([[typing_pred]], [xx], uu____4565)  in
            let uu____4598 =
              let uu____4613 = FStar_TypeChecker_Env.get_range env  in
              let uu____4614 = mkForall_fuel1 env  in uu____4614 uu____4613
               in
            uu____4598 uu____4554  in
          (uu____4553, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4545  in
      let uu____4636 =
        let uu____4639 =
          let uu____4640 =
            let uu____4648 =
              let uu____4649 =
                let uu____4660 =
                  let uu____4661 =
                    let uu____4666 =
                      let uu____4667 =
                        let uu____4670 =
                          let uu____4673 =
                            let uu____4676 =
                              let uu____4677 =
                                let uu____4682 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____4683 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____4682, uu____4683)  in
                              FStar_SMTEncoding_Util.mkGT uu____4677  in
                            let uu____4685 =
                              let uu____4688 =
                                let uu____4689 =
                                  let uu____4694 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____4695 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____4694, uu____4695)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4689  in
                              let uu____4697 =
                                let uu____4700 =
                                  let uu____4701 =
                                    let uu____4706 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____4707 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____4706, uu____4707)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4701  in
                                [uu____4700]  in
                              uu____4688 :: uu____4697  in
                            uu____4676 :: uu____4685  in
                          typing_pred_y :: uu____4673  in
                        typing_pred :: uu____4670  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4667  in
                    (uu____4666, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4661  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4660)
                 in
              let uu____4740 =
                let uu____4755 = FStar_TypeChecker_Env.get_range env  in
                let uu____4756 = mkForall_fuel1 env  in uu____4756 uu____4755
                 in
              uu____4740 uu____4649  in
            (uu____4648,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4640  in
        [uu____4639]  in
      uu____4544 :: uu____4636  in
    uu____4480 :: uu____4541  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4803 =
      let uu____4804 =
        let uu____4812 =
          let uu____4813 = FStar_TypeChecker_Env.get_range env  in
          let uu____4814 =
            let uu____4825 =
              let uu____4830 =
                let uu____4833 = FStar_SMTEncoding_Term.boxString b  in
                [uu____4833]  in
              [uu____4830]  in
            let uu____4838 =
              let uu____4839 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4839 tt  in
            (uu____4825, [bb], uu____4838)  in
          FStar_SMTEncoding_Term.mkForall uu____4813 uu____4814  in
        (uu____4812, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4804  in
    let uu____4864 =
      let uu____4867 =
        let uu____4868 =
          let uu____4876 =
            let uu____4877 =
              let uu____4888 =
                let uu____4889 =
                  let uu____4894 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____4894)  in
                FStar_SMTEncoding_Util.mkImp uu____4889  in
              ([[typing_pred]], [xx], uu____4888)  in
            let uu____4921 =
              let uu____4936 = FStar_TypeChecker_Env.get_range env  in
              let uu____4937 = mkForall_fuel1 env  in uu____4937 uu____4936
               in
            uu____4921 uu____4877  in
          (uu____4876, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4868  in
      [uu____4867]  in
    uu____4803 :: uu____4864  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____4984 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____4984]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____5014 =
      let uu____5015 =
        let uu____5023 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____5023, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5015  in
    [uu____5014]  in
  let mk_and_interp env conj uu____5046 =
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
    let uu____5075 =
      let uu____5076 =
        let uu____5084 =
          let uu____5085 = FStar_TypeChecker_Env.get_range env  in
          let uu____5086 =
            let uu____5097 =
              let uu____5098 =
                let uu____5103 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____5103, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5098  in
            ([[l_and_a_b]], [aa; bb], uu____5097)  in
          FStar_SMTEncoding_Term.mkForall uu____5085 uu____5086  in
        (uu____5084, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5076  in
    [uu____5075]  in
  let mk_or_interp env disj uu____5158 =
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
    let uu____5187 =
      let uu____5188 =
        let uu____5196 =
          let uu____5197 = FStar_TypeChecker_Env.get_range env  in
          let uu____5198 =
            let uu____5209 =
              let uu____5210 =
                let uu____5215 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5215, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5210  in
            ([[l_or_a_b]], [aa; bb], uu____5209)  in
          FStar_SMTEncoding_Term.mkForall uu____5197 uu____5198  in
        (uu____5196, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5188  in
    [uu____5187]  in
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
    let uu____5293 =
      let uu____5294 =
        let uu____5302 =
          let uu____5303 = FStar_TypeChecker_Env.get_range env  in
          let uu____5304 =
            let uu____5315 =
              let uu____5316 =
                let uu____5321 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5321, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5316  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5315)  in
          FStar_SMTEncoding_Term.mkForall uu____5303 uu____5304  in
        (uu____5302, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5294  in
    [uu____5293]  in
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
    let uu____5411 =
      let uu____5412 =
        let uu____5420 =
          let uu____5421 = FStar_TypeChecker_Env.get_range env  in
          let uu____5422 =
            let uu____5433 =
              let uu____5434 =
                let uu____5439 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5439, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5434  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5433)  in
          FStar_SMTEncoding_Term.mkForall uu____5421 uu____5422  in
        (uu____5420, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5412  in
    [uu____5411]  in
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
    let uu____5539 =
      let uu____5540 =
        let uu____5548 =
          let uu____5549 = FStar_TypeChecker_Env.get_range env  in
          let uu____5550 =
            let uu____5561 =
              let uu____5562 =
                let uu____5567 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____5567, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5562  in
            ([[l_imp_a_b]], [aa; bb], uu____5561)  in
          FStar_SMTEncoding_Term.mkForall uu____5549 uu____5550  in
        (uu____5548, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5540  in
    [uu____5539]  in
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
    let uu____5651 =
      let uu____5652 =
        let uu____5660 =
          let uu____5661 = FStar_TypeChecker_Env.get_range env  in
          let uu____5662 =
            let uu____5673 =
              let uu____5674 =
                let uu____5679 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____5679, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5674  in
            ([[l_iff_a_b]], [aa; bb], uu____5673)  in
          FStar_SMTEncoding_Term.mkForall uu____5661 uu____5662  in
        (uu____5660, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5652  in
    [uu____5651]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____5750 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____5750  in
    let uu____5755 =
      let uu____5756 =
        let uu____5764 =
          let uu____5765 = FStar_TypeChecker_Env.get_range env  in
          let uu____5766 =
            let uu____5777 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____5777)  in
          FStar_SMTEncoding_Term.mkForall uu____5765 uu____5766  in
        (uu____5764, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5756  in
    [uu____5755]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____5830 =
      let uu____5831 =
        let uu____5839 =
          let uu____5840 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____5840 range_ty  in
        let uu____5841 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____5839, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____5841)
         in
      FStar_SMTEncoding_Util.mkAssume uu____5831  in
    [uu____5830]  in
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
        let uu____5887 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____5887 x1 t  in
      let uu____5889 = FStar_TypeChecker_Env.get_range env  in
      let uu____5890 =
        let uu____5901 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____5901)  in
      FStar_SMTEncoding_Term.mkForall uu____5889 uu____5890  in
    let uu____5926 =
      let uu____5927 =
        let uu____5935 =
          let uu____5936 = FStar_TypeChecker_Env.get_range env  in
          let uu____5937 =
            let uu____5948 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____5948)  in
          FStar_SMTEncoding_Term.mkForall uu____5936 uu____5937  in
        (uu____5935,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5927  in
    [uu____5926]  in
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
    let uu____6009 =
      let uu____6010 =
        let uu____6018 =
          let uu____6019 = FStar_TypeChecker_Env.get_range env  in
          let uu____6020 =
            let uu____6036 =
              let uu____6037 =
                let uu____6042 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____6043 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____6042, uu____6043)  in
              FStar_SMTEncoding_Util.mkAnd uu____6037  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____6036)
             in
          FStar_SMTEncoding_Term.mkForall' uu____6019 uu____6020  in
        (uu____6018,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6010  in
    [uu____6009]  in
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
          let uu____6601 =
            FStar_Util.find_opt
              (fun uu____6639  ->
                 match uu____6639 with
                 | (l,uu____6655) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____6601 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____6698,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____6759 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____6759 with
        | (form,decls) ->
            let uu____6768 =
              let uu____6771 =
                let uu____6774 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____6774]  in
              FStar_All.pipe_right uu____6771
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____6768
  
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
              let uu____6833 =
                ((let uu____6837 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____6837) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____6833
              then
                let arg_sorts =
                  let uu____6849 =
                    let uu____6850 = FStar_Syntax_Subst.compress t_norm  in
                    uu____6850.FStar_Syntax_Syntax.n  in
                  match uu____6849 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6856) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6894  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6901 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6903 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6903 with
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
                    let uu____6935 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____6935, env1)
              else
                (let uu____6940 = prims.is lid  in
                 if uu____6940
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6949 = prims.mk lid vname  in
                   match uu____6949 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____6973 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____6973, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6982 =
                      let uu____7001 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____7001 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7029 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7029
                            then
                              let uu____7034 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___295_7037 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___295_7037.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___295_7037.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___295_7037.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___295_7037.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___295_7037.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___295_7037.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___295_7037.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___295_7037.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___295_7037.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___295_7037.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___295_7037.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___295_7037.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___295_7037.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___295_7037.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___295_7037.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___295_7037.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___295_7037.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___295_7037.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___295_7037.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___295_7037.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___295_7037.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___295_7037.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___295_7037.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___295_7037.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___295_7037.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___295_7037.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___295_7037.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___295_7037.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___295_7037.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___295_7037.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___295_7037.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___295_7037.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___295_7037.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___295_7037.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___295_7037.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___295_7037.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___295_7037.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___295_7037.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___295_7037.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___295_7037.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___295_7037.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___295_7037.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7034
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7060 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____7060)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6982 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_7166  ->
                                  match uu___0_7166 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7170 = FStar_Util.prefix vars
                                         in
                                      (match uu____7170 with
                                       | (uu____7203,xxv) ->
                                           let xx =
                                             let uu____7242 =
                                               let uu____7243 =
                                                 let uu____7249 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7249,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7243
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7242
                                              in
                                           let uu____7252 =
                                             let uu____7253 =
                                               let uu____7261 =
                                                 let uu____7262 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7263 =
                                                   let uu____7274 =
                                                     let uu____7275 =
                                                       let uu____7280 =
                                                         let uu____7281 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7281
                                                          in
                                                       (vapp, uu____7280)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7275
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7274)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7262 uu____7263
                                                  in
                                               (uu____7261,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7253
                                              in
                                           [uu____7252])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7296 = FStar_Util.prefix vars
                                         in
                                      (match uu____7296 with
                                       | (uu____7329,xxv) ->
                                           let xx =
                                             let uu____7368 =
                                               let uu____7369 =
                                                 let uu____7375 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7375,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7369
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7368
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
                                           let uu____7386 =
                                             let uu____7387 =
                                               let uu____7395 =
                                                 let uu____7396 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7397 =
                                                   let uu____7408 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7408)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7396 uu____7397
                                                  in
                                               (uu____7395,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7387
                                              in
                                           [uu____7386])
                                  | uu____7421 -> []))
                           in
                        let uu____7422 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7422 with
                         | (vars,guards,env',decls1,uu____7447) ->
                             let uu____7460 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7473 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7473, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7477 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7477 with
                                    | (g,ds) ->
                                        let uu____7490 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7490,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7460 with
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
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10388,
                                                              uu____10389)
                                                          else
                                                            (let uu____10400
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10400))
                                                           in
                                                        (match uu____10337
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10424
                                                                 =
                                                                 let uu____10432
                                                                   =
                                                                   let uu____10433
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10434
                                                                    =
                                                                    let uu____10445
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10445)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10433
                                                                    uu____10434
                                                                    in
                                                                 let uu____10454
                                                                   =
                                                                   let uu____10455
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10455
                                                                    in
                                                                 (uu____10432,
                                                                   uu____10454,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10424
                                                                in
                                                             let uu____10461
                                                               =
                                                               let uu____10464
                                                                 =
                                                                 let uu____10467
                                                                   =
                                                                   let uu____10470
                                                                    =
                                                                    let uu____10473
                                                                    =
                                                                    let uu____10476
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10476
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10473
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10470
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10467
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10464
                                                                in
                                                             (uu____10461,
                                                               env2)))))))
                               | uu____10485 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10545 =
                                   let uu____10551 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____10551,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10545  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10557 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10610  ->
                                         fun fvb  ->
                                           match uu____10610 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10665 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10665
                                                  in
                                               let gtok =
                                                 let uu____10669 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10669
                                                  in
                                               let env4 =
                                                 let uu____10672 =
                                                   let uu____10675 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _10681  ->
                                                        FStar_Pervasives_Native.Some
                                                          _10681) uu____10675
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10672
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10557 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10801
                                     t_norm uu____10803 =
                                     match (uu____10801, uu____10803) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10833;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10834;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10836;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10837;_})
                                         ->
                                         let uu____10864 =
                                           let uu____10871 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10871 with
                                           | (tcenv',uu____10887,e_t) ->
                                               let uu____10893 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10904 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10893 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___727_10921 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___727_10921.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10864 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10934 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10934
                                                then
                                                  let uu____10939 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10941 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10943 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10939 uu____10941
                                                    uu____10943
                                                else ());
                                               (let uu____10948 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____10948 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____10975 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____10975 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____10997 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____10997
                                                           then
                                                             let uu____11002
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11004
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11007
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11009
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11002
                                                               uu____11004
                                                               uu____11007
                                                               uu____11009
                                                           else ());
                                                          (let uu____11014 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11014
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11043)
                                                               ->
                                                               let uu____11056
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11069
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11069,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11073
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11073
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11086
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11086,
                                                                    decls0))
                                                                  in
                                                               (match uu____11056
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
                                                                    let uu____11107
                                                                    =
                                                                    let uu____11119
                                                                    =
                                                                    let uu____11122
                                                                    =
                                                                    let uu____11125
                                                                    =
                                                                    let uu____11128
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11128
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11125
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11122
                                                                     in
                                                                    (g,
                                                                    uu____11119,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11107
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
                                                                    let uu____11158
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11158
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
                                                                    let uu____11173
                                                                    =
                                                                    let uu____11176
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11176
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11173
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11182
                                                                    =
                                                                    let uu____11185
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11185
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11182
                                                                     in
                                                                    let uu____11190
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11190
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11206
                                                                    =
                                                                    let uu____11214
                                                                    =
                                                                    let uu____11215
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11216
                                                                    =
                                                                    let uu____11232
                                                                    =
                                                                    let uu____11233
                                                                    =
                                                                    let uu____11238
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11238)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11233
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11232)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11215
                                                                    uu____11216
                                                                     in
                                                                    let uu____11252
                                                                    =
                                                                    let uu____11253
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11253
                                                                     in
                                                                    (uu____11214,
                                                                    uu____11252,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11206
                                                                     in
                                                                    let eqn_f
                                                                    =
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
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11281)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11269
                                                                    uu____11270
                                                                     in
                                                                    (uu____11268,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11260
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11295
                                                                    =
                                                                    let uu____11303
                                                                    =
                                                                    let uu____11304
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11305
                                                                    =
                                                                    let uu____11316
                                                                    =
                                                                    let uu____11317
                                                                    =
                                                                    let uu____11322
                                                                    =
                                                                    let uu____11323
                                                                    =
                                                                    let uu____11326
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11326
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11323
                                                                     in
                                                                    (gsapp,
                                                                    uu____11322)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11317
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11316)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11304
                                                                    uu____11305
                                                                     in
                                                                    (uu____11303,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11295
                                                                     in
                                                                    let uu____11340
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
                                                                    let uu____11352
                                                                    =
                                                                    let uu____11353
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11353
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11352
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____11355
                                                                    =
                                                                    let uu____11363
                                                                    =
                                                                    let uu____11364
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11365
                                                                    =
                                                                    let uu____11376
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11376)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11364
                                                                    uu____11365
                                                                     in
                                                                    (uu____11363,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11355
                                                                     in
                                                                    let uu____11389
                                                                    =
                                                                    let uu____11398
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11398
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11413
                                                                    =
                                                                    let uu____11416
                                                                    =
                                                                    let uu____11417
                                                                    =
                                                                    let uu____11425
                                                                    =
                                                                    let uu____11426
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11427
                                                                    =
                                                                    let uu____11438
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11438)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11426
                                                                    uu____11427
                                                                     in
                                                                    (uu____11425,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11417
                                                                     in
                                                                    [uu____11416]
                                                                     in
                                                                    (d3,
                                                                    uu____11413)
                                                                     in
                                                                    match uu____11389
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11340
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11495
                                                                    =
                                                                    let uu____11498
                                                                    =
                                                                    let uu____11501
                                                                    =
                                                                    let uu____11504
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11504
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11501
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11498
                                                                     in
                                                                    let uu____11511
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11495,
                                                                    uu____11511,
                                                                    env02))))))))))
                                      in
                                   let uu____11516 =
                                     let uu____11529 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11592  ->
                                          fun uu____11593  ->
                                            match (uu____11592, uu____11593)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11718 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11718 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11529
                                      in
                                   (match uu____11516 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11785 =
                                          let isDeclFun uu___1_11802 =
                                            match uu___1_11802 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11804 -> true
                                            | uu____11817 -> false  in
                                          let uu____11819 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11819
                                            (fun decls3  ->
                                               let uu____11849 =
                                                 FStar_List.fold_left
                                                   (fun uu____11880  ->
                                                      fun elt  ->
                                                        match uu____11880
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____11921 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____11921
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____11949
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____11949
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
                                                                    let uu___820_11987
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___820_11987.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___820_11987.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___820_11987.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____11849 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12019 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12019, elts, rest))
                                           in
                                        (match uu____11785 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12048 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12054  ->
                                        match uu___2_12054 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12057 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12065 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12065)))
                                in
                             if uu____12048
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___837_12087  ->
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
                   let uu____12126 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12126
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12145 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12145, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12201 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12201 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12207 = encode_sigelt' env se  in
      match uu____12207 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12219 =
                  let uu____12222 =
                    let uu____12223 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12223  in
                  [uu____12222]  in
                FStar_All.pipe_right uu____12219
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12228 ->
                let uu____12229 =
                  let uu____12232 =
                    let uu____12235 =
                      let uu____12236 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12236  in
                    [uu____12235]  in
                  FStar_All.pipe_right uu____12232
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12243 =
                  let uu____12246 =
                    let uu____12249 =
                      let uu____12252 =
                        let uu____12253 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12253  in
                      [uu____12252]  in
                    FStar_All.pipe_right uu____12249
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12246  in
                FStar_List.append uu____12229 uu____12243
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12267 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12267
       then
         let uu____12272 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12272
       else ());
      (let is_opaque_to_smt t =
         let uu____12284 =
           let uu____12285 = FStar_Syntax_Subst.compress t  in
           uu____12285.FStar_Syntax_Syntax.n  in
         match uu____12284 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12290)) -> s = "opaque_to_smt"
         | uu____12295 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12304 =
           let uu____12305 = FStar_Syntax_Subst.compress t  in
           uu____12305.FStar_Syntax_Syntax.n  in
         match uu____12304 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12310)) -> s = "uninterpreted_by_smt"
         | uu____12315 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12321 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12327 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12339 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12340 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12341 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12354 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12356 =
             let uu____12358 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12358  in
           if uu____12356
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12387 ->
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
                  let uu____12420 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____12420  in
                let uu____12421 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12421 with
                | (formals,uu____12441) ->
                    let arity = FStar_List.length formals  in
                    let uu____12465 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12465 with
                     | (aname,atok,env2) ->
                         let uu____12487 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____12487 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12503 =
                                  let uu____12504 =
                                    let uu____12516 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____12536  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12516,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12504
                                   in
                                [uu____12503;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____12553 =
                                let aux uu____12599 uu____12600 =
                                  match (uu____12599, uu____12600) with
                                  | ((bv,uu____12644),(env3,acc_sorts,acc))
                                      ->
                                      let uu____12676 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____12676 with
                                       | (xxsym,xx,env4) ->
                                           let uu____12699 =
                                             let uu____12702 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____12702 :: acc_sorts  in
                                           (env4, uu____12699, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____12553 with
                               | (uu____12734,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____12750 =
                                       let uu____12758 =
                                         let uu____12759 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12760 =
                                           let uu____12771 =
                                             let uu____12772 =
                                               let uu____12777 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____12777)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____12772
                                              in
                                           ([[app]], xs_sorts, uu____12771)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12759 uu____12760
                                          in
                                       (uu____12758,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12750
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____12792 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____12792
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____12795 =
                                       let uu____12803 =
                                         let uu____12804 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____12805 =
                                           let uu____12816 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____12816)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12804 uu____12805
                                          in
                                       (uu____12803,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____12795
                                      in
                                   let uu____12829 =
                                     let uu____12832 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____12832  in
                                   (env2, uu____12829))))
                 in
              let uu____12841 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____12841 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12867,uu____12868)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____12869 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____12869 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12891,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____12898 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_12904  ->
                       match uu___3_12904 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____12907 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____12913 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____12916 -> false))
                in
             Prims.op_Negation uu____12898  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____12926 =
                let uu____12931 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____12931 env fv t quals  in
              match uu____12926 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____12945 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____12945  in
                  let uu____12948 =
                    let uu____12949 =
                      let uu____12952 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____12952
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____12949  in
                  (uu____12948, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____12962 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____12962 with
            | (uvs,f1) ->
                let env1 =
                  let uu___974_12974 = env  in
                  let uu____12975 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___974_12974.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___974_12974.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___974_12974.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____12975;
                    FStar_SMTEncoding_Env.warn =
                      (uu___974_12974.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___974_12974.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___974_12974.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___974_12974.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___974_12974.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___974_12974.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___974_12974.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____12977 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____12977 with
                 | (f3,decls) ->
                     let g =
                       let uu____12991 =
                         let uu____12994 =
                           let uu____12995 =
                             let uu____13003 =
                               let uu____13004 =
                                 let uu____13006 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13006
                                  in
                               FStar_Pervasives_Native.Some uu____13004  in
                             let uu____13010 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13003, uu____13010)  in
                           FStar_SMTEncoding_Util.mkAssume uu____12995  in
                         [uu____12994]  in
                       FStar_All.pipe_right uu____12991
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13019) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13033 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13055 =
                        let uu____13058 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13058.FStar_Syntax_Syntax.fv_name  in
                      uu____13055.FStar_Syntax_Syntax.v  in
                    let uu____13059 =
                      let uu____13061 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13061  in
                    if uu____13059
                    then
                      let val_decl =
                        let uu___991_13093 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___991_13093.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___991_13093.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___991_13093.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____13094 = encode_sigelt' env1 val_decl  in
                      match uu____13094 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13033 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13130,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13132;
                           FStar_Syntax_Syntax.lbtyp = uu____13133;
                           FStar_Syntax_Syntax.lbeff = uu____13134;
                           FStar_Syntax_Syntax.lbdef = uu____13135;
                           FStar_Syntax_Syntax.lbattrs = uu____13136;
                           FStar_Syntax_Syntax.lbpos = uu____13137;_}::[]),uu____13138)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13157 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____13157 with
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
                  let uu____13195 =
                    let uu____13198 =
                      let uu____13199 =
                        let uu____13207 =
                          let uu____13208 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13209 =
                            let uu____13220 =
                              let uu____13221 =
                                let uu____13226 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13226)  in
                              FStar_SMTEncoding_Util.mkEq uu____13221  in
                            ([[b2t_x]], [xx], uu____13220)  in
                          FStar_SMTEncoding_Term.mkForall uu____13208
                            uu____13209
                           in
                        (uu____13207,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13199  in
                    [uu____13198]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13195
                   in
                let uu____13264 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13264, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13267,uu____13268) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13278  ->
                   match uu___4_13278 with
                   | FStar_Syntax_Syntax.Discriminator uu____13280 -> true
                   | uu____13282 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13284,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13296 =
                      let uu____13298 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13298.FStar_Ident.idText  in
                    uu____13296 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13305  ->
                      match uu___5_13305 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13308 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13311) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13325  ->
                   match uu___6_13325 with
                   | FStar_Syntax_Syntax.Projector uu____13327 -> true
                   | uu____13333 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13337 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13337 with
            | FStar_Pervasives_Native.Some uu____13344 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1056_13346 = se  in
                  let uu____13347 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13347;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1056_13346.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1056_13346.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1056_13346.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13350) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1068_13371 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1068_13371.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1068_13371.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1068_13371.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1068_13371.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1068_13371.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13376) ->
           let uu____13385 = encode_sigelts env ses  in
           (match uu____13385 with
            | (g,env1) ->
                let uu____13396 =
                  FStar_List.fold_left
                    (fun uu____13420  ->
                       fun elt  ->
                         match uu____13420 with
                         | (g',inversions) ->
                             let uu____13448 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_13471  ->
                                       match uu___7_13471 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13473;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13474;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13475;_}
                                           -> false
                                       | uu____13482 -> true))
                                in
                             (match uu____13448 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1094_13507 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1094_13507.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1094_13507.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1094_13507.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13396 with
                 | (g',inversions) ->
                     let uu____13526 =
                       FStar_List.fold_left
                         (fun uu____13557  ->
                            fun elt  ->
                              match uu____13557 with
                              | (decls,elts,rest) ->
                                  let uu____13598 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_13607  ->
                                            match uu___8_13607 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____13609 -> true
                                            | uu____13622 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____13598
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____13645 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_13666  ->
                                               match uu___9_13666 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____13668 -> true
                                               | uu____13681 -> false))
                                        in
                                     match uu____13645 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1116_13712 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1116_13712.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1116_13712.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1116_13712.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____13526 with
                      | (decls,elts,rest) ->
                          let uu____13738 =
                            let uu____13739 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____13746 =
                              let uu____13749 =
                                let uu____13752 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____13752  in
                              FStar_List.append elts uu____13749  in
                            FStar_List.append uu____13739 uu____13746  in
                          (uu____13738, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____13763,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____13776 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____13776 with
             | (usubst,uvs) ->
                 let uu____13796 =
                   let uu____13803 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____13804 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____13805 =
                     let uu____13806 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____13806 k  in
                   (uu____13803, uu____13804, uu____13805)  in
                 (match uu____13796 with
                  | (env1,tps1,k1) ->
                      let uu____13819 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____13819 with
                       | (tps2,k2) ->
                           let uu____13827 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____13827 with
                            | (uu____13843,k3) ->
                                let uu____13865 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____13865 with
                                 | (tps3,env_tps,uu____13877,us) ->
                                     let u_k =
                                       let uu____13880 =
                                         let uu____13881 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____13882 =
                                           let uu____13887 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____13889 =
                                             let uu____13890 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____13890
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____13887 uu____13889
                                            in
                                         uu____13882
                                           FStar_Pervasives_Native.None
                                           uu____13881
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____13880 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____13908) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____13914,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____13917) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____13925,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____13932) ->
                                           let uu____13933 =
                                             let uu____13935 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13935
                                              in
                                           failwith uu____13933
                                       | (uu____13939,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____13940 =
                                             let uu____13942 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13942
                                              in
                                           failwith uu____13940
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____13946,uu____13947) ->
                                           let uu____13956 =
                                             let uu____13958 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13958
                                              in
                                           failwith uu____13956
                                       | (uu____13962,FStar_Syntax_Syntax.U_unif
                                          uu____13963) ->
                                           let uu____13972 =
                                             let uu____13974 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____13974
                                              in
                                           failwith uu____13972
                                       | uu____13978 -> false  in
                                     let u_leq_u_k u =
                                       let uu____13991 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____13991 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14009 = u_leq_u_k u_tp  in
                                       if uu____14009
                                       then true
                                       else
                                         (let uu____14016 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14016 with
                                          | (formals,uu____14033) ->
                                              let uu____14054 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14054 with
                                               | (uu____14064,uu____14065,uu____14066,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14077 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14077
             then
               let uu____14082 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14082
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14102  ->
                       match uu___10_14102 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14106 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14119 = c  in
                 match uu____14119 with
                 | (name,args,uu____14124,uu____14125,uu____14126) ->
                     let uu____14137 =
                       let uu____14138 =
                         let uu____14150 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14177  ->
                                   match uu____14177 with
                                   | (uu____14186,sort,uu____14188) -> sort))
                            in
                         (name, uu____14150,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14138  in
                     [uu____14137]
               else
                 (let uu____14199 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14199 c)
                in
             let inversion_axioms tapp vars =
               let uu____14217 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14225 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14225 FStar_Option.isNone))
                  in
               if uu____14217
               then []
               else
                 (let uu____14260 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14260 with
                  | (xxsym,xx) ->
                      let uu____14273 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14312  ->
                                fun l  ->
                                  match uu____14312 with
                                  | (out,decls) ->
                                      let uu____14332 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14332 with
                                       | (uu____14343,data_t) ->
                                           let uu____14345 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14345 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14389 =
                                                    let uu____14390 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14390.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14389 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14393,indices)
                                                      -> indices
                                                  | uu____14419 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14449  ->
                                                            match uu____14449
                                                            with
                                                            | (x,uu____14457)
                                                                ->
                                                                let uu____14462
                                                                  =
                                                                  let uu____14463
                                                                    =
                                                                    let uu____14471
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14471,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14463
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14462)
                                                       env)
                                                   in
                                                let uu____14476 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14476 with
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
                                                                  let uu____14511
                                                                    =
                                                                    let uu____14516
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____14516,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____14511)
                                                             vars indices1
                                                         else []  in
                                                       let uu____14519 =
                                                         let uu____14520 =
                                                           let uu____14525 =
                                                             let uu____14526
                                                               =
                                                               let uu____14531
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____14532
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____14531,
                                                                 uu____14532)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____14526
                                                              in
                                                           (out, uu____14525)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____14520
                                                          in
                                                       (uu____14519,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14273 with
                       | (data_ax,decls) ->
                           let uu____14547 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____14547 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____14564 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____14564 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____14571 =
                                    let uu____14579 =
                                      let uu____14580 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____14581 =
                                        let uu____14592 =
                                          let uu____14593 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____14595 =
                                            let uu____14598 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____14598 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____14593 uu____14595
                                           in
                                        let uu____14600 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____14592,
                                          uu____14600)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____14580 uu____14581
                                       in
                                    let uu____14609 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____14579,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____14609)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____14571
                                   in
                                let uu____14615 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____14615)))
                in
             let uu____14622 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____14644 ->
                     let uu____14645 =
                       let uu____14652 =
                         let uu____14653 =
                           let uu____14668 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____14668)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____14653  in
                       FStar_Syntax_Syntax.mk uu____14652  in
                     uu____14645 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____14622 with
             | (formals,res) ->
                 let uu____14708 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____14708 with
                  | (vars,guards,env',binder_decls,uu____14733) ->
                      let arity = FStar_List.length vars  in
                      let uu____14747 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____14747 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____14773 =
                               let uu____14781 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____14781)  in
                             FStar_SMTEncoding_Util.mkApp uu____14773  in
                           let uu____14787 =
                             let tname_decl =
                               let uu____14797 =
                                 let uu____14798 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____14817 =
                                             let uu____14819 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____14819
                                              in
                                           let uu____14821 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____14817, uu____14821, false)))
                                    in
                                 let uu____14825 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____14798,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____14825, false)
                                  in
                               constructor_or_logic_type_decl uu____14797  in
                             let uu____14833 =
                               match vars with
                               | [] ->
                                   let uu____14846 =
                                     let uu____14847 =
                                       let uu____14850 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _14856  ->
                                            FStar_Pervasives_Native.Some
                                              _14856) uu____14850
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____14847
                                      in
                                   ([], uu____14846)
                               | uu____14859 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____14869 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____14869
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____14885 =
                                       let uu____14893 =
                                         let uu____14894 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14895 =
                                           let uu____14911 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____14911)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____14894 uu____14895
                                          in
                                       (uu____14893,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____14885
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____14833 with
                             | (tok_decls,env2) ->
                                 let uu____14938 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____14938
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____14787 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____14966 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____14966 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____14988 =
                                            let uu____14989 =
                                              let uu____14997 =
                                                let uu____14998 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____14998
                                                 in
                                              (uu____14997,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____14989
                                             in
                                          [uu____14988]
                                        else []  in
                                      let uu____15006 =
                                        let uu____15009 =
                                          let uu____15012 =
                                            let uu____15015 =
                                              let uu____15016 =
                                                let uu____15024 =
                                                  let uu____15025 =
                                                    FStar_Ident.range_of_lid
                                                      t
                                                     in
                                                  let uu____15026 =
                                                    let uu____15037 =
                                                      FStar_SMTEncoding_Util.mkImp
                                                        (guard, k1)
                                                       in
                                                    ([[tapp]], vars,
                                                      uu____15037)
                                                     in
                                                  FStar_SMTEncoding_Term.mkForall
                                                    uu____15025 uu____15026
                                                   in
                                                (uu____15024,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15016
                                               in
                                            [uu____15015]  in
                                          FStar_List.append karr uu____15012
                                           in
                                        FStar_All.pipe_right uu____15009
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15006
                                   in
                                let aux =
                                  let uu____15056 =
                                    let uu____15059 =
                                      inversion_axioms tapp vars  in
                                    let uu____15062 =
                                      let uu____15065 =
                                        let uu____15068 =
                                          let uu____15069 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15069 env2 tapp
                                            vars
                                           in
                                        [uu____15068]  in
                                      FStar_All.pipe_right uu____15065
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15059 uu____15062
                                     in
                                  FStar_List.append kindingAx uu____15056  in
                                let g =
                                  let uu____15077 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15077
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15085,uu____15086,uu____15087,uu____15088,uu____15089)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15097,t,uu____15099,n_tps,uu____15101) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15112 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15112 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15160 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15160 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15184 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15184 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15204 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15204 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15283 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15283,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15290 =
                                   let uu____15291 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15291, true)
                                    in
                                 let uu____15299 =
                                   let uu____15306 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15306
                                    in
                                 FStar_All.pipe_right uu____15290 uu____15299
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
                               let uu____15318 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15318 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15330::uu____15331 ->
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
                                            let uu____15380 =
                                              let uu____15381 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15381]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15380
                                             in
                                          let uu____15407 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15408 =
                                            let uu____15419 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15419)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15407 uu____15408
                                      | uu____15446 -> tok_typing  in
                                    let uu____15457 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15457 with
                                     | (vars',guards',env'',decls_formals,uu____15482)
                                         ->
                                         let uu____15495 =
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
                                         (match uu____15495 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____15525 ->
                                                    let uu____15534 =
                                                      let uu____15535 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____15535
                                                       in
                                                    [uu____15534]
                                                 in
                                              let encode_elim uu____15551 =
                                                let uu____15552 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____15552 with
                                                | (head1,args) ->
                                                    let uu____15603 =
                                                      let uu____15604 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____15604.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____15603 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____15616;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____15617;_},uu____15618)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____15624 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____15624
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
                                                                  | uu____15687
                                                                    ->
                                                                    let uu____15688
                                                                    =
                                                                    let uu____15694
                                                                    =
                                                                    let uu____15696
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15696
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15694)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15688
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15719
                                                                    =
                                                                    let uu____15721
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15721
                                                                     in
                                                                    if
                                                                    uu____15719
                                                                    then
                                                                    let uu____15743
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15743]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____15746
                                                                =
                                                                let uu____15760
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____15817
                                                                     ->
                                                                    fun
                                                                    uu____15818
                                                                     ->
                                                                    match 
                                                                    (uu____15817,
                                                                    uu____15818)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15929
                                                                    =
                                                                    let uu____15937
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15937
                                                                     in
                                                                    (match uu____15929
                                                                    with
                                                                    | 
                                                                    (uu____15951,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15962
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15962
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15967
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15967
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
                                                                  uu____15760
                                                                 in
                                                              (match uu____15746
                                                               with
                                                               | (uu____15988,arg_vars,elim_eqns_or_guards,uu____15991)
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
                                                                    let uu____16018
                                                                    =
                                                                    let uu____16026
                                                                    =
                                                                    let uu____16027
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16028
                                                                    =
                                                                    let uu____16039
                                                                    =
                                                                    let uu____16040
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16040
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16042
                                                                    =
                                                                    let uu____16043
                                                                    =
                                                                    let uu____16048
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16048)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16043
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16039,
                                                                    uu____16042)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16027
                                                                    uu____16028
                                                                     in
                                                                    (uu____16026,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16018
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16063
                                                                    =
                                                                    let uu____16064
                                                                    =
                                                                    let uu____16070
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16070,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16064
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16063
                                                                     in
                                                                    let uu____16073
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16073
                                                                    then
                                                                    let x =
                                                                    let uu____16077
                                                                    =
                                                                    let uu____16083
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16083,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16077
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16088
                                                                    =
                                                                    let uu____16096
                                                                    =
                                                                    let uu____16097
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16098
                                                                    =
                                                                    let uu____16109
                                                                    =
                                                                    let uu____16114
                                                                    =
                                                                    let uu____16117
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16117]
                                                                     in
                                                                    [uu____16114]
                                                                     in
                                                                    let uu____16122
                                                                    =
                                                                    let uu____16123
                                                                    =
                                                                    let uu____16128
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16130
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16128,
                                                                    uu____16130)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16123
                                                                     in
                                                                    (uu____16109,
                                                                    [x],
                                                                    uu____16122)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16097
                                                                    uu____16098
                                                                     in
                                                                    let uu____16151
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16096,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16151)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16088
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16162
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
                                                                    (let uu____16185
                                                                    =
                                                                    let uu____16186
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16186
                                                                    dapp1  in
                                                                    [uu____16185])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16162
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16193
                                                                    =
                                                                    let uu____16201
                                                                    =
                                                                    let uu____16202
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16203
                                                                    =
                                                                    let uu____16214
                                                                    =
                                                                    let uu____16215
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16215
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16217
                                                                    =
                                                                    let uu____16218
                                                                    =
                                                                    let uu____16223
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16223)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16218
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16214,
                                                                    uu____16217)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16202
                                                                    uu____16203
                                                                     in
                                                                    (uu____16201,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16193)
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
                                                         let uu____16242 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16242
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
                                                                  | uu____16305
                                                                    ->
                                                                    let uu____16306
                                                                    =
                                                                    let uu____16312
                                                                    =
                                                                    let uu____16314
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16314
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16312)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16306
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16337
                                                                    =
                                                                    let uu____16339
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16339
                                                                     in
                                                                    if
                                                                    uu____16337
                                                                    then
                                                                    let uu____16361
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16361]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16364
                                                                =
                                                                let uu____16378
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16435
                                                                     ->
                                                                    fun
                                                                    uu____16436
                                                                     ->
                                                                    match 
                                                                    (uu____16435,
                                                                    uu____16436)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16547
                                                                    =
                                                                    let uu____16555
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16555
                                                                     in
                                                                    (match uu____16547
                                                                    with
                                                                    | 
                                                                    (uu____16569,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16580
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16580
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16585
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16585
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
                                                                  uu____16378
                                                                 in
                                                              (match uu____16364
                                                               with
                                                               | (uu____16606,arg_vars,elim_eqns_or_guards,uu____16609)
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
                                                                    let uu____16636
                                                                    =
                                                                    let uu____16644
                                                                    =
                                                                    let uu____16645
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16646
                                                                    =
                                                                    let uu____16657
                                                                    =
                                                                    let uu____16658
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16658
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16660
                                                                    =
                                                                    let uu____16661
                                                                    =
                                                                    let uu____16666
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16666)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16661
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16657,
                                                                    uu____16660)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16645
                                                                    uu____16646
                                                                     in
                                                                    (uu____16644,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16636
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16681
                                                                    =
                                                                    let uu____16682
                                                                    =
                                                                    let uu____16688
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16688,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16682
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16681
                                                                     in
                                                                    let uu____16691
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16691
                                                                    then
                                                                    let x =
                                                                    let uu____16695
                                                                    =
                                                                    let uu____16701
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16701,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16695
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16706
                                                                    =
                                                                    let uu____16714
                                                                    =
                                                                    let uu____16715
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16716
                                                                    =
                                                                    let uu____16727
                                                                    =
                                                                    let uu____16732
                                                                    =
                                                                    let uu____16735
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16735]
                                                                     in
                                                                    [uu____16732]
                                                                     in
                                                                    let uu____16740
                                                                    =
                                                                    let uu____16741
                                                                    =
                                                                    let uu____16746
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16748
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16746,
                                                                    uu____16748)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16741
                                                                     in
                                                                    (uu____16727,
                                                                    [x],
                                                                    uu____16740)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16715
                                                                    uu____16716
                                                                     in
                                                                    let uu____16769
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16714,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16769)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16706
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16780
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
                                                                    (let uu____16803
                                                                    =
                                                                    let uu____16804
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16804
                                                                    dapp1  in
                                                                    [uu____16803])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16780
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16811
                                                                    =
                                                                    let uu____16819
                                                                    =
                                                                    let uu____16820
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16821
                                                                    =
                                                                    let uu____16832
                                                                    =
                                                                    let uu____16833
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16833
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16835
                                                                    =
                                                                    let uu____16836
                                                                    =
                                                                    let uu____16841
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16841)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16836
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16832,
                                                                    uu____16835)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16820
                                                                    uu____16821
                                                                     in
                                                                    (uu____16819,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16811)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____16858 ->
                                                         ((let uu____16860 =
                                                             let uu____16866
                                                               =
                                                               let uu____16868
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____16870
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____16868
                                                                 uu____16870
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____16866)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____16860);
                                                          ([], [])))
                                                 in
                                              let uu____16878 =
                                                encode_elim ()  in
                                              (match uu____16878 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____16904 =
                                                       let uu____16907 =
                                                         let uu____16910 =
                                                           let uu____16913 =
                                                             let uu____16916
                                                               =
                                                               let uu____16919
                                                                 =
                                                                 let uu____16922
                                                                   =
                                                                   let uu____16923
                                                                    =
                                                                    let uu____16935
                                                                    =
                                                                    let uu____16936
                                                                    =
                                                                    let uu____16938
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16938
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____16936
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____16935)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____16923
                                                                    in
                                                                 [uu____16922]
                                                                  in
                                                               FStar_List.append
                                                                 uu____16919
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____16916
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____16949 =
                                                             let uu____16952
                                                               =
                                                               let uu____16955
                                                                 =
                                                                 let uu____16958
                                                                   =
                                                                   let uu____16961
                                                                    =
                                                                    let uu____16964
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____16969
                                                                    =
                                                                    let uu____16972
                                                                    =
                                                                    let uu____16973
                                                                    =
                                                                    let uu____16981
                                                                    =
                                                                    let uu____16982
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16983
                                                                    =
                                                                    let uu____16994
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16994)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16982
                                                                    uu____16983
                                                                     in
                                                                    (uu____16981,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16973
                                                                     in
                                                                    let uu____17007
                                                                    =
                                                                    let uu____17010
                                                                    =
                                                                    let uu____17011
                                                                    =
                                                                    let uu____17019
                                                                    =
                                                                    let uu____17020
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17021
                                                                    =
                                                                    let uu____17032
                                                                    =
                                                                    let uu____17033
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17033
                                                                    vars'  in
                                                                    let uu____17035
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17032,
                                                                    uu____17035)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17020
                                                                    uu____17021
                                                                     in
                                                                    (uu____17019,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17011
                                                                     in
                                                                    [uu____17010]
                                                                     in
                                                                    uu____16972
                                                                    ::
                                                                    uu____17007
                                                                     in
                                                                    uu____16964
                                                                    ::
                                                                    uu____16969
                                                                     in
                                                                   FStar_List.append
                                                                    uu____16961
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____16958
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____16955
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____16952
                                                              in
                                                           FStar_List.append
                                                             uu____16913
                                                             uu____16949
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____16910
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____16907
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____16904
                                                      in
                                                   let uu____17052 =
                                                     let uu____17053 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17053 g
                                                      in
                                                   (uu____17052, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17087  ->
              fun se  ->
                match uu____17087 with
                | (g,env1) ->
                    let uu____17107 = encode_sigelt env1 se  in
                    (match uu____17107 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17175 =
        match uu____17175 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17212 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17220 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17220
                   then
                     let uu____17225 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17227 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17229 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17225 uu____17227 uu____17229
                   else ());
                  (let uu____17234 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17234 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17252 =
                         let uu____17260 =
                           let uu____17262 =
                             let uu____17264 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17264
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17262  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17260
                          in
                       (match uu____17252 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17284 = FStar_Options.log_queries ()
                                 in
                              if uu____17284
                              then
                                let uu____17287 =
                                  let uu____17289 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17291 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17293 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17289 uu____17291 uu____17293
                                   in
                                FStar_Pervasives_Native.Some uu____17287
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17309 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17319 =
                                let uu____17322 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17322  in
                              FStar_List.append uu____17309 uu____17319  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17334,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17354 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17354 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____17375 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____17375 with | (uu____17402,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17455  ->
              match uu____17455 with
              | (l,uu____17464,uu____17465) ->
                  let uu____17468 =
                    let uu____17480 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17480, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17468))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17513  ->
              match uu____17513 with
              | (l,uu____17524,uu____17525) ->
                  let uu____17528 =
                    let uu____17529 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _17532  -> FStar_SMTEncoding_Term.Echo _17532)
                      uu____17529
                     in
                  let uu____17533 =
                    let uu____17536 =
                      let uu____17537 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17537  in
                    [uu____17536]  in
                  uu____17528 :: uu____17533))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17555 =
      let uu____17558 =
        let uu____17559 = FStar_Util.psmap_empty ()  in
        let uu____17574 =
          let uu____17583 = FStar_Util.psmap_empty ()  in (uu____17583, [])
           in
        let uu____17590 =
          let uu____17592 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____17592 FStar_Ident.string_of_lid  in
        let uu____17594 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17559;
          FStar_SMTEncoding_Env.fvar_bindings = uu____17574;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____17590;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____17594
        }  in
      [uu____17558]  in
    FStar_ST.op_Colon_Equals last_env uu____17555
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____17638 = FStar_ST.op_Bang last_env  in
      match uu____17638 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17666 ->
          let uu___1540_17669 = e  in
          let uu____17670 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1540_17669.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1540_17669.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1540_17669.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1540_17669.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1540_17669.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1540_17669.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1540_17669.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____17670;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1540_17669.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1540_17669.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____17678 = FStar_ST.op_Bang last_env  in
    match uu____17678 with
    | [] -> failwith "Empty env stack"
    | uu____17705::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____17737  ->
    let uu____17738 = FStar_ST.op_Bang last_env  in
    match uu____17738 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____17798  ->
    let uu____17799 = FStar_ST.op_Bang last_env  in
    match uu____17799 with
    | [] -> failwith "Popping an empty stack"
    | uu____17826::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____17863  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____17916  ->
         let uu____17917 = snapshot_env ()  in
         match uu____17917 with
         | (env_depth,()) ->
             let uu____17939 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____17939 with
              | (varops_depth,()) ->
                  let uu____17961 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____17961 with
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
        (fun uu____18019  ->
           let uu____18020 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18020 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18115 = snapshot msg  in () 
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
        | (uu____18161::uu____18162,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1601_18170 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1601_18170.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1601_18170.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1601_18170.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18171 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1607_18198 = elt  in
        let uu____18199 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1607_18198.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1607_18198.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18199;
          FStar_SMTEncoding_Term.a_names =
            (uu___1607_18198.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18219 =
        let uu____18222 =
          let uu____18223 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18223  in
        let uu____18224 = open_fact_db_tags env  in uu____18222 ::
          uu____18224
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18219
  
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
      let uu____18251 = encode_sigelt env se  in
      match uu____18251 with
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
                (let uu____18297 =
                   let uu____18300 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18300
                    in
                 match uu____18297 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18315 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18315
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18345 = FStar_Options.log_queries ()  in
        if uu____18345
        then
          let uu____18350 =
            let uu____18351 =
              let uu____18353 =
                let uu____18355 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18355 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18353  in
            FStar_SMTEncoding_Term.Caption uu____18351  in
          uu____18350 :: decls
        else decls  in
      (let uu____18374 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18374
       then
         let uu____18377 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18377
       else ());
      (let env =
         let uu____18383 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18383 tcenv  in
       let uu____18384 = encode_top_level_facts env se  in
       match uu____18384 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18398 =
               let uu____18401 =
                 let uu____18404 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18404
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18401  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18398)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18437 = FStar_Options.log_queries ()  in
          if uu____18437
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1645_18457 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1645_18457.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1645_18457.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1645_18457.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1645_18457.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1645_18457.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1645_18457.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1645_18457.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1645_18457.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1645_18457.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1645_18457.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18462 =
             let uu____18465 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18465
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18462  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18485 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18485
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
          (let uu____18509 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____18509
           then
             let uu____18512 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____18512
           else ());
          (let env =
             let uu____18520 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____18520
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____18559  ->
                     fun se  ->
                       match uu____18559 with
                       | (g,env2) ->
                           let uu____18579 = encode_top_level_facts env2 se
                              in
                           (match uu____18579 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____18602 =
             encode_signature
               (let uu___1668_18611 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1668_18611.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1668_18611.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1668_18611.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1668_18611.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1668_18611.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1668_18611.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1668_18611.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1668_18611.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1668_18611.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1668_18611.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____18602 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____18627 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18627
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____18633 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____18633))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____18661  ->
        match uu____18661 with
        | (decls,fvbs) ->
            ((let uu____18675 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____18675
              then ()
              else
                (let uu____18680 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18680
                 then
                   let uu____18683 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____18683
                 else ()));
             (let env =
                let uu____18691 = get_env name tcenv  in
                FStar_All.pipe_right uu____18691
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____18693 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____18693
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____18707 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____18707
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
        (let uu____18769 =
           let uu____18771 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____18771.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____18769);
        (let env =
           let uu____18773 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____18773 tcenv  in
         let uu____18774 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____18813 = aux rest  in
                 (match uu____18813 with
                  | (out,rest1) ->
                      let t =
                        let uu____18841 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____18841 with
                        | FStar_Pervasives_Native.Some uu____18844 ->
                            let uu____18845 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____18845
                              x.FStar_Syntax_Syntax.sort
                        | uu____18846 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding true;
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
         match uu____18774 with
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
  