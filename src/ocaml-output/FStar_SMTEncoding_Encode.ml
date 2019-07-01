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
                  let tot_fun_axioms =
                    let all_vars_but_one =
                      FStar_All.pipe_right (FStar_Util.prefix vars)
                        FStar_Pervasives_Native.fst
                       in
                    let axiom_name = Prims.op_Hat "primitive_tot_fun_" x1  in
                    let tot_fun_axiom_for_x =
                      let uu____390 =
                        let uu____398 =
                          FStar_SMTEncoding_Term.mk_IsTotFun xtok1  in
                        (uu____398, FStar_Pervasives_Native.None, axiom_name)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____390  in
                    let uu____401 =
                      FStar_List.fold_left
                        (fun uu____455  ->
                           fun var  ->
                             match uu____455 with
                             | (axioms,app,vars1) ->
                                 let app1 =
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply app
                                     [var]
                                    in
                                 let vars2 = FStar_List.append vars1 [var]
                                    in
                                 let axiom_name1 =
                                   let uu____582 =
                                     let uu____584 =
                                       let uu____586 =
                                         FStar_All.pipe_right vars2
                                           FStar_List.length
                                          in
                                       Prims.string_of_int uu____586  in
                                     Prims.op_Hat "." uu____584  in
                                   Prims.op_Hat axiom_name uu____582  in
                                 let uu____608 =
                                   let uu____611 =
                                     let uu____614 =
                                       let uu____615 =
                                         let uu____623 =
                                           let uu____624 =
                                             let uu____635 =
                                               FStar_SMTEncoding_Term.mk_IsTotFun
                                                 app1
                                                in
                                             ([[app1]], vars2, uu____635)  in
                                           FStar_SMTEncoding_Term.mkForall
                                             rng uu____624
                                            in
                                         (uu____623,
                                           FStar_Pervasives_Native.None,
                                           axiom_name1)
                                          in
                                       FStar_SMTEncoding_Util.mkAssume
                                         uu____615
                                        in
                                     [uu____614]  in
                                   FStar_List.append axioms uu____611  in
                                 (uu____608, app1, vars2))
                        ([tot_fun_axiom_for_x], xtok1, []) all_vars_but_one
                       in
                    match uu____401 with
                    | (axioms,uu____681,uu____682) -> axioms  in
                  let uu____707 =
                    let uu____710 =
                      let uu____713 =
                        let uu____716 =
                          let uu____719 =
                            let uu____720 =
                              let uu____728 =
                                let uu____729 =
                                  let uu____740 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body)
                                     in
                                  ([[xapp]], vars, uu____740)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____729
                                 in
                              (uu____728, FStar_Pervasives_Native.None,
                                (Prims.op_Hat "primitive_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____720  in
                          [uu____719]  in
                        xtok_decl :: uu____716  in
                      xname_decl :: uu____713  in
                    let uu____752 =
                      let uu____755 =
                        let uu____758 =
                          let uu____759 =
                            let uu____767 =
                              let uu____768 =
                                let uu____779 =
                                  FStar_SMTEncoding_Util.mkEq
                                    (xtok_app, xapp)
                                   in
                                ([[xtok_app]], vars, uu____779)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____768
                               in
                            (uu____767,
                              (FStar_Pervasives_Native.Some
                                 "Name-token correspondence"),
                              (Prims.op_Hat "token_correspondence_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____759  in
                        [uu____758]  in
                      FStar_List.append tot_fun_axioms uu____755  in
                    FStar_List.append uu____710 uu____752  in
                  (xtok1, (FStar_List.length vars), uu____707)  in
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
                  let uu____949 =
                    let uu____970 =
                      let uu____989 =
                        let uu____990 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____990
                         in
                      quant axy uu____989  in
                    (FStar_Parser_Const.op_Eq, uu____970)  in
                  let uu____1007 =
                    let uu____1030 =
                      let uu____1051 =
                        let uu____1070 =
                          let uu____1071 =
                            let uu____1072 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____1072  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____1071
                           in
                        quant axy uu____1070  in
                      (FStar_Parser_Const.op_notEq, uu____1051)  in
                    let uu____1089 =
                      let uu____1112 =
                        let uu____1133 =
                          let uu____1152 =
                            let uu____1153 =
                              let uu____1154 =
                                let uu____1159 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____1160 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____1159, uu____1160)  in
                              FStar_SMTEncoding_Util.mkAnd uu____1154  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____1153
                             in
                          quant xy uu____1152  in
                        (FStar_Parser_Const.op_And, uu____1133)  in
                      let uu____1177 =
                        let uu____1200 =
                          let uu____1221 =
                            let uu____1240 =
                              let uu____1241 =
                                let uu____1242 =
                                  let uu____1247 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____1248 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____1247, uu____1248)  in
                                FStar_SMTEncoding_Util.mkOr uu____1242  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1241
                               in
                            quant xy uu____1240  in
                          (FStar_Parser_Const.op_Or, uu____1221)  in
                        let uu____1265 =
                          let uu____1288 =
                            let uu____1309 =
                              let uu____1328 =
                                let uu____1329 =
                                  let uu____1330 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____1330  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1329
                                 in
                              quant qx uu____1328  in
                            (FStar_Parser_Const.op_Negation, uu____1309)  in
                          let uu____1347 =
                            let uu____1370 =
                              let uu____1391 =
                                let uu____1410 =
                                  let uu____1411 =
                                    let uu____1412 =
                                      let uu____1417 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1418 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1417, uu____1418)  in
                                    FStar_SMTEncoding_Util.mkLT uu____1412
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1411
                                   in
                                quant xy uu____1410  in
                              (FStar_Parser_Const.op_LT, uu____1391)  in
                            let uu____1435 =
                              let uu____1458 =
                                let uu____1479 =
                                  let uu____1498 =
                                    let uu____1499 =
                                      let uu____1500 =
                                        let uu____1505 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1506 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1505, uu____1506)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1500
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1499
                                     in
                                  quant xy uu____1498  in
                                (FStar_Parser_Const.op_LTE, uu____1479)  in
                              let uu____1523 =
                                let uu____1546 =
                                  let uu____1567 =
                                    let uu____1586 =
                                      let uu____1587 =
                                        let uu____1588 =
                                          let uu____1593 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1594 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1593, uu____1594)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1588
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1587
                                       in
                                    quant xy uu____1586  in
                                  (FStar_Parser_Const.op_GT, uu____1567)  in
                                let uu____1611 =
                                  let uu____1634 =
                                    let uu____1655 =
                                      let uu____1674 =
                                        let uu____1675 =
                                          let uu____1676 =
                                            let uu____1681 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1682 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1681, uu____1682)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1676
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1675
                                         in
                                      quant xy uu____1674  in
                                    (FStar_Parser_Const.op_GTE, uu____1655)
                                     in
                                  let uu____1699 =
                                    let uu____1722 =
                                      let uu____1743 =
                                        let uu____1762 =
                                          let uu____1763 =
                                            let uu____1764 =
                                              let uu____1769 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1770 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1769, uu____1770)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1764
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1763
                                           in
                                        quant xy uu____1762  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1743)
                                       in
                                    let uu____1787 =
                                      let uu____1810 =
                                        let uu____1831 =
                                          let uu____1850 =
                                            let uu____1851 =
                                              let uu____1852 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1852
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1851
                                             in
                                          quant qx uu____1850  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1831)
                                         in
                                      let uu____1869 =
                                        let uu____1892 =
                                          let uu____1913 =
                                            let uu____1932 =
                                              let uu____1933 =
                                                let uu____1934 =
                                                  let uu____1939 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1940 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1939, uu____1940)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1934
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1933
                                               in
                                            quant xy uu____1932  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1913)
                                           in
                                        let uu____1957 =
                                          let uu____1980 =
                                            let uu____2001 =
                                              let uu____2020 =
                                                let uu____2021 =
                                                  let uu____2022 =
                                                    let uu____2027 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____2028 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____2027, uu____2028)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____2022
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____2021
                                                 in
                                              quant xy uu____2020  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____2001)
                                             in
                                          let uu____2045 =
                                            let uu____2068 =
                                              let uu____2089 =
                                                let uu____2108 =
                                                  let uu____2109 =
                                                    let uu____2110 =
                                                      let uu____2115 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____2116 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____2115,
                                                        uu____2116)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____2110
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____2109
                                                   in
                                                quant xy uu____2108  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____2089)
                                               in
                                            let uu____2133 =
                                              let uu____2156 =
                                                let uu____2177 =
                                                  let uu____2196 =
                                                    let uu____2197 =
                                                      let uu____2198 =
                                                        let uu____2203 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____2204 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____2203,
                                                          uu____2204)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____2198
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____2197
                                                     in
                                                  quant xy uu____2196  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____2177)
                                                 in
                                              let uu____2221 =
                                                let uu____2244 =
                                                  let uu____2265 =
                                                    let uu____2284 =
                                                      let uu____2285 =
                                                        let uu____2286 =
                                                          let uu____2291 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____2292 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____2291,
                                                            uu____2292)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____2286
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____2285
                                                       in
                                                    quant xy uu____2284  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____2265)
                                                   in
                                                let uu____2309 =
                                                  let uu____2332 =
                                                    let uu____2353 =
                                                      let uu____2372 =
                                                        let uu____2373 =
                                                          let uu____2374 =
                                                            let uu____2379 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____2380 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____2379,
                                                              uu____2380)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____2374
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____2373
                                                         in
                                                      quant xy uu____2372  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____2353)
                                                     in
                                                  let uu____2397 =
                                                    let uu____2420 =
                                                      let uu____2441 =
                                                        let uu____2460 =
                                                          let uu____2461 =
                                                            let uu____2462 =
                                                              let uu____2467
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2468
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2467,
                                                                uu____2468)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2462
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2461
                                                           in
                                                        quant xy uu____2460
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2441)
                                                       in
                                                    let uu____2485 =
                                                      let uu____2508 =
                                                        let uu____2529 =
                                                          let uu____2548 =
                                                            let uu____2549 =
                                                              let uu____2550
                                                                =
                                                                let uu____2555
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2556
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2555,
                                                                  uu____2556)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2550
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2549
                                                             in
                                                          quant xy uu____2548
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2529)
                                                         in
                                                      let uu____2573 =
                                                        let uu____2596 =
                                                          let uu____2617 =
                                                            let uu____2636 =
                                                              let uu____2637
                                                                =
                                                                let uu____2638
                                                                  =
                                                                  let uu____2643
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2644
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2643,
                                                                    uu____2644)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2638
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2637
                                                               in
                                                            quant xy
                                                              uu____2636
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2617)
                                                           in
                                                        let uu____2661 =
                                                          let uu____2684 =
                                                            let uu____2705 =
                                                              let uu____2724
                                                                =
                                                                let uu____2725
                                                                  =
                                                                  let uu____2726
                                                                    =
                                                                    let uu____2731
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2732
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2731,
                                                                    uu____2732)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2726
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2725
                                                                 in
                                                              quant xy
                                                                uu____2724
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2705)
                                                             in
                                                          let uu____2749 =
                                                            let uu____2772 =
                                                              let uu____2793
                                                                =
                                                                let uu____2812
                                                                  =
                                                                  let uu____2813
                                                                    =
                                                                    let uu____2814
                                                                    =
                                                                    let uu____2819
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2820
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2819,
                                                                    uu____2820)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2814
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2813
                                                                   in
                                                                quant xy
                                                                  uu____2812
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2793)
                                                               in
                                                            let uu____2837 =
                                                              let uu____2860
                                                                =
                                                                let uu____2881
                                                                  =
                                                                  let uu____2900
                                                                    =
                                                                    let uu____2901
                                                                    =
                                                                    let uu____2902
                                                                    =
                                                                    let uu____2907
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2908
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2907,
                                                                    uu____2908)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2902
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2901
                                                                     in
                                                                  quant xy
                                                                    uu____2900
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2881)
                                                                 in
                                                              let uu____2925
                                                                =
                                                                let uu____2948
                                                                  =
                                                                  let uu____2969
                                                                    =
                                                                    let uu____2988
                                                                    =
                                                                    let uu____2989
                                                                    =
                                                                    let uu____2990
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____2990
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2989
                                                                     in
                                                                    quant qx
                                                                    uu____2988
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____2969)
                                                                   in
                                                                [uu____2948]
                                                                 in
                                                              uu____2860 ::
                                                                uu____2925
                                                               in
                                                            uu____2772 ::
                                                              uu____2837
                                                             in
                                                          uu____2684 ::
                                                            uu____2749
                                                           in
                                                        uu____2596 ::
                                                          uu____2661
                                                         in
                                                      uu____2508 ::
                                                        uu____2573
                                                       in
                                                    uu____2420 :: uu____2485
                                                     in
                                                  uu____2332 :: uu____2397
                                                   in
                                                uu____2244 :: uu____2309  in
                                              uu____2156 :: uu____2221  in
                                            uu____2068 :: uu____2133  in
                                          uu____1980 :: uu____2045  in
                                        uu____1892 :: uu____1957  in
                                      uu____1810 :: uu____1869  in
                                    uu____1722 :: uu____1787  in
                                  uu____1634 :: uu____1699  in
                                uu____1546 :: uu____1611  in
                              uu____1458 :: uu____1523  in
                            uu____1370 :: uu____1435  in
                          uu____1288 :: uu____1347  in
                        uu____1200 :: uu____1265  in
                      uu____1112 :: uu____1177  in
                    uu____1030 :: uu____1089  in
                  uu____949 :: uu____1007  in
                let mk1 l v1 =
                  let uu____3529 =
                    let uu____3541 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____3631  ->
                              match uu____3631 with
                              | (l',uu____3652) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3541
                      (FStar_Option.map
                         (fun uu____3751  ->
                            match uu____3751 with
                            | (uu____3779,b) ->
                                let uu____3813 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3813 v1))
                     in
                  FStar_All.pipe_right uu____3529 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____3896  ->
                          match uu____3896 with
                          | (l',uu____3917) -> FStar_Ident.lid_equals l l'))
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
          let uu____3991 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3991 with
          | (xxsym,xx) ->
              let uu____4002 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____4002 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____4018 =
                     let uu____4026 =
                       let uu____4027 =
                         let uu____4038 =
                           let uu____4039 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____4049 =
                             let uu____4060 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____4060 :: vars  in
                           uu____4039 :: uu____4049  in
                         let uu____4086 =
                           let uu____4087 =
                             let uu____4092 =
                               let uu____4093 =
                                 let uu____4098 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____4098)  in
                               FStar_SMTEncoding_Util.mkEq uu____4093  in
                             (xx_has_type, uu____4092)  in
                           FStar_SMTEncoding_Util.mkImp uu____4087  in
                         ([[xx_has_type]], uu____4038, uu____4086)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____4027  in
                     let uu____4111 =
                       let uu____4113 =
                         let uu____4115 =
                           let uu____4117 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____4117  in
                         Prims.op_Hat module_name uu____4115  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____4113
                        in
                     (uu____4026, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____4111)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____4018)
  
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
    let uu____4173 =
      let uu____4175 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____4175  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4173  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____4197 =
      let uu____4198 =
        let uu____4206 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____4206, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4198  in
    let uu____4211 =
      let uu____4214 =
        let uu____4215 =
          let uu____4223 =
            let uu____4224 =
              let uu____4235 =
                let uu____4236 =
                  let uu____4241 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____4241)  in
                FStar_SMTEncoding_Util.mkImp uu____4236  in
              ([[typing_pred]], [xx], uu____4235)  in
            let uu____4266 =
              let uu____4281 = FStar_TypeChecker_Env.get_range env  in
              let uu____4282 = mkForall_fuel1 env  in uu____4282 uu____4281
               in
            uu____4266 uu____4224  in
          (uu____4223, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4215  in
      [uu____4214]  in
    uu____4197 :: uu____4211  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4329 =
      let uu____4330 =
        let uu____4338 =
          let uu____4339 = FStar_TypeChecker_Env.get_range env  in
          let uu____4340 =
            let uu____4351 =
              let uu____4356 =
                let uu____4359 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____4359]  in
              [uu____4356]  in
            let uu____4364 =
              let uu____4365 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4365 tt  in
            (uu____4351, [bb], uu____4364)  in
          FStar_SMTEncoding_Term.mkForall uu____4339 uu____4340  in
        (uu____4338, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4330  in
    let uu____4390 =
      let uu____4393 =
        let uu____4394 =
          let uu____4402 =
            let uu____4403 =
              let uu____4414 =
                let uu____4415 =
                  let uu____4420 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____4420)  in
                FStar_SMTEncoding_Util.mkImp uu____4415  in
              ([[typing_pred]], [xx], uu____4414)  in
            let uu____4447 =
              let uu____4462 = FStar_TypeChecker_Env.get_range env  in
              let uu____4463 = mkForall_fuel1 env  in uu____4463 uu____4462
               in
            uu____4447 uu____4403  in
          (uu____4402, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4394  in
      [uu____4393]  in
    uu____4329 :: uu____4390  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____4506 =
        let uu____4507 =
          let uu____4513 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4513, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4507  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4506  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4527 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4527  in
    let uu____4532 =
      let uu____4533 =
        let uu____4541 =
          let uu____4542 = FStar_TypeChecker_Env.get_range env  in
          let uu____4543 =
            let uu____4554 =
              let uu____4559 =
                let uu____4562 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4562]  in
              [uu____4559]  in
            let uu____4567 =
              let uu____4568 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4568 tt  in
            (uu____4554, [bb], uu____4567)  in
          FStar_SMTEncoding_Term.mkForall uu____4542 uu____4543  in
        (uu____4541, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4533  in
    let uu____4593 =
      let uu____4596 =
        let uu____4597 =
          let uu____4605 =
            let uu____4606 =
              let uu____4617 =
                let uu____4618 =
                  let uu____4623 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4623)  in
                FStar_SMTEncoding_Util.mkImp uu____4618  in
              ([[typing_pred]], [xx], uu____4617)  in
            let uu____4650 =
              let uu____4665 = FStar_TypeChecker_Env.get_range env  in
              let uu____4666 = mkForall_fuel1 env  in uu____4666 uu____4665
               in
            uu____4650 uu____4606  in
          (uu____4605, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4597  in
      let uu____4688 =
        let uu____4691 =
          let uu____4692 =
            let uu____4700 =
              let uu____4701 =
                let uu____4712 =
                  let uu____4713 =
                    let uu____4718 =
                      let uu____4719 =
                        let uu____4722 =
                          let uu____4725 =
                            let uu____4728 =
                              let uu____4729 =
                                let uu____4734 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4735 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____4734, uu____4735)  in
                              FStar_SMTEncoding_Util.mkGT uu____4729  in
                            let uu____4737 =
                              let uu____4740 =
                                let uu____4741 =
                                  let uu____4746 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4747 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____4746, uu____4747)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4741  in
                              let uu____4749 =
                                let uu____4752 =
                                  let uu____4753 =
                                    let uu____4758 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4759 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4758, uu____4759)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4753  in
                                [uu____4752]  in
                              uu____4740 :: uu____4749  in
                            uu____4728 :: uu____4737  in
                          typing_pred_y :: uu____4725  in
                        typing_pred :: uu____4722  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4719  in
                    (uu____4718, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4713  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4712)
                 in
              let uu____4792 =
                let uu____4807 = FStar_TypeChecker_Env.get_range env  in
                let uu____4808 = mkForall_fuel1 env  in uu____4808 uu____4807
                 in
              uu____4792 uu____4701  in
            (uu____4700,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4692  in
        [uu____4691]  in
      uu____4596 :: uu____4688  in
    uu____4532 :: uu____4593  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____4851 =
        let uu____4852 =
          let uu____4858 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4858, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4852  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4851  in
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
      let uu____4874 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4874  in
    let uu____4879 =
      let uu____4880 =
        let uu____4888 =
          let uu____4889 = FStar_TypeChecker_Env.get_range env  in
          let uu____4890 =
            let uu____4901 =
              let uu____4906 =
                let uu____4909 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4909]  in
              [uu____4906]  in
            let uu____4914 =
              let uu____4915 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4915 tt  in
            (uu____4901, [bb], uu____4914)  in
          FStar_SMTEncoding_Term.mkForall uu____4889 uu____4890  in
        (uu____4888, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4880  in
    let uu____4940 =
      let uu____4943 =
        let uu____4944 =
          let uu____4952 =
            let uu____4953 =
              let uu____4964 =
                let uu____4965 =
                  let uu____4970 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____4970)  in
                FStar_SMTEncoding_Util.mkImp uu____4965  in
              ([[typing_pred]], [xx], uu____4964)  in
            let uu____4997 =
              let uu____5012 = FStar_TypeChecker_Env.get_range env  in
              let uu____5013 = mkForall_fuel1 env  in uu____5013 uu____5012
               in
            uu____4997 uu____4953  in
          (uu____4952, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4944  in
      let uu____5035 =
        let uu____5038 =
          let uu____5039 =
            let uu____5047 =
              let uu____5048 =
                let uu____5059 =
                  let uu____5060 =
                    let uu____5065 =
                      let uu____5066 =
                        let uu____5069 =
                          let uu____5072 =
                            let uu____5075 =
                              let uu____5076 =
                                let uu____5081 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____5082 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____5081, uu____5082)  in
                              FStar_SMTEncoding_Util.mkGT uu____5076  in
                            let uu____5084 =
                              let uu____5087 =
                                let uu____5088 =
                                  let uu____5093 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____5094 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____5093, uu____5094)  in
                                FStar_SMTEncoding_Util.mkGTE uu____5088  in
                              let uu____5096 =
                                let uu____5099 =
                                  let uu____5100 =
                                    let uu____5105 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____5106 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____5105, uu____5106)  in
                                  FStar_SMTEncoding_Util.mkLT uu____5100  in
                                [uu____5099]  in
                              uu____5087 :: uu____5096  in
                            uu____5075 :: uu____5084  in
                          typing_pred_y :: uu____5072  in
                        typing_pred :: uu____5069  in
                      FStar_SMTEncoding_Util.mk_and_l uu____5066  in
                    (uu____5065, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____5060  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____5059)
                 in
              let uu____5139 =
                let uu____5154 = FStar_TypeChecker_Env.get_range env  in
                let uu____5155 = mkForall_fuel1 env  in uu____5155 uu____5154
                 in
              uu____5139 uu____5048  in
            (uu____5047,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____5039  in
        [uu____5038]  in
      uu____4943 :: uu____5035  in
    uu____4879 :: uu____4940  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____5202 =
      let uu____5203 =
        let uu____5211 =
          let uu____5212 = FStar_TypeChecker_Env.get_range env  in
          let uu____5213 =
            let uu____5224 =
              let uu____5229 =
                let uu____5232 = FStar_SMTEncoding_Term.boxString b  in
                [uu____5232]  in
              [uu____5229]  in
            let uu____5237 =
              let uu____5238 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____5238 tt  in
            (uu____5224, [bb], uu____5237)  in
          FStar_SMTEncoding_Term.mkForall uu____5212 uu____5213  in
        (uu____5211, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5203  in
    let uu____5263 =
      let uu____5266 =
        let uu____5267 =
          let uu____5275 =
            let uu____5276 =
              let uu____5287 =
                let uu____5288 =
                  let uu____5293 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____5293)  in
                FStar_SMTEncoding_Util.mkImp uu____5288  in
              ([[typing_pred]], [xx], uu____5287)  in
            let uu____5320 =
              let uu____5335 = FStar_TypeChecker_Env.get_range env  in
              let uu____5336 = mkForall_fuel1 env  in uu____5336 uu____5335
               in
            uu____5320 uu____5276  in
          (uu____5275, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____5267  in
      [uu____5266]  in
    uu____5202 :: uu____5263  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____5383 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____5383]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____5413 =
      let uu____5414 =
        let uu____5422 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____5422, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5414  in
    [uu____5413]  in
  let mk_and_interp env conj uu____5445 =
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
    let uu____5474 =
      let uu____5475 =
        let uu____5483 =
          let uu____5484 = FStar_TypeChecker_Env.get_range env  in
          let uu____5485 =
            let uu____5496 =
              let uu____5497 =
                let uu____5502 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____5502, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5497  in
            ([[l_and_a_b]], [aa; bb], uu____5496)  in
          FStar_SMTEncoding_Term.mkForall uu____5484 uu____5485  in
        (uu____5483, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5475  in
    [uu____5474]  in
  let mk_or_interp env disj uu____5557 =
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
    let uu____5586 =
      let uu____5587 =
        let uu____5595 =
          let uu____5596 = FStar_TypeChecker_Env.get_range env  in
          let uu____5597 =
            let uu____5608 =
              let uu____5609 =
                let uu____5614 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5614, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5609  in
            ([[l_or_a_b]], [aa; bb], uu____5608)  in
          FStar_SMTEncoding_Term.mkForall uu____5596 uu____5597  in
        (uu____5595, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5587  in
    [uu____5586]  in
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
    let uu____5692 =
      let uu____5693 =
        let uu____5701 =
          let uu____5702 = FStar_TypeChecker_Env.get_range env  in
          let uu____5703 =
            let uu____5714 =
              let uu____5715 =
                let uu____5720 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5720, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5715  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5714)  in
          FStar_SMTEncoding_Term.mkForall uu____5702 uu____5703  in
        (uu____5701, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5693  in
    [uu____5692]  in
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
    let uu____5810 =
      let uu____5811 =
        let uu____5819 =
          let uu____5820 = FStar_TypeChecker_Env.get_range env  in
          let uu____5821 =
            let uu____5832 =
              let uu____5833 =
                let uu____5838 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5838, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5833  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5832)  in
          FStar_SMTEncoding_Term.mkForall uu____5820 uu____5821  in
        (uu____5819, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5811  in
    [uu____5810]  in
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
    let uu____5938 =
      let uu____5939 =
        let uu____5947 =
          let uu____5948 = FStar_TypeChecker_Env.get_range env  in
          let uu____5949 =
            let uu____5960 =
              let uu____5961 =
                let uu____5966 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____5966, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5961  in
            ([[l_imp_a_b]], [aa; bb], uu____5960)  in
          FStar_SMTEncoding_Term.mkForall uu____5948 uu____5949  in
        (uu____5947, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5939  in
    [uu____5938]  in
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
    let uu____6050 =
      let uu____6051 =
        let uu____6059 =
          let uu____6060 = FStar_TypeChecker_Env.get_range env  in
          let uu____6061 =
            let uu____6072 =
              let uu____6073 =
                let uu____6078 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____6078, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____6073  in
            ([[l_iff_a_b]], [aa; bb], uu____6072)  in
          FStar_SMTEncoding_Term.mkForall uu____6060 uu____6061  in
        (uu____6059, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6051  in
    [uu____6050]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____6149 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____6149  in
    let uu____6154 =
      let uu____6155 =
        let uu____6163 =
          let uu____6164 = FStar_TypeChecker_Env.get_range env  in
          let uu____6165 =
            let uu____6176 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____6176)  in
          FStar_SMTEncoding_Term.mkForall uu____6164 uu____6165  in
        (uu____6163, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6155  in
    [uu____6154]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____6229 =
      let uu____6230 =
        let uu____6238 =
          let uu____6239 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____6239 range_ty  in
        let uu____6240 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____6238, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____6240)
         in
      FStar_SMTEncoding_Util.mkAssume uu____6230  in
    [uu____6229]  in
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
        let uu____6286 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____6286 x1 t  in
      let uu____6288 = FStar_TypeChecker_Env.get_range env  in
      let uu____6289 =
        let uu____6300 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____6300)  in
      FStar_SMTEncoding_Term.mkForall uu____6288 uu____6289  in
    let uu____6325 =
      let uu____6326 =
        let uu____6334 =
          let uu____6335 = FStar_TypeChecker_Env.get_range env  in
          let uu____6336 =
            let uu____6347 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____6347)  in
          FStar_SMTEncoding_Term.mkForall uu____6335 uu____6336  in
        (uu____6334,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6326  in
    [uu____6325]  in
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
    let uu____6408 =
      let uu____6409 =
        let uu____6417 =
          let uu____6418 = FStar_TypeChecker_Env.get_range env  in
          let uu____6419 =
            let uu____6435 =
              let uu____6436 =
                let uu____6441 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____6442 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____6441, uu____6442)  in
              FStar_SMTEncoding_Util.mkAnd uu____6436  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____6435)
             in
          FStar_SMTEncoding_Term.mkForall' uu____6418 uu____6419  in
        (uu____6417,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6409  in
    [uu____6408]  in
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
          let uu____7000 =
            FStar_Util.find_opt
              (fun uu____7038  ->
                 match uu____7038 with
                 | (l,uu____7054) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____7000 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____7097,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____7158 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____7158 with
        | (form,decls) ->
            let uu____7167 =
              let uu____7170 =
                let uu____7173 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____7173]  in
              FStar_All.pipe_right uu____7170
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____7167
  
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
              let uu____7232 =
                ((let uu____7236 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____7236) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____7232
              then
                let arg_sorts =
                  let uu____7248 =
                    let uu____7249 = FStar_Syntax_Subst.compress t_norm  in
                    uu____7249.FStar_Syntax_Syntax.n  in
                  match uu____7248 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____7255) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____7293  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____7300 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____7302 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____7302 with
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
                    let uu____7334 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____7334, env1)
              else
                (let uu____7339 = prims.is lid  in
                 if uu____7339
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____7348 = prims.mk lid vname  in
                   match uu____7348 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____7372 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____7372, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____7381 =
                      let uu____7400 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____7400 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7428 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7428
                            then
                              let uu____7433 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___311_7436 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___311_7436.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___311_7436.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___311_7436.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___311_7436.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___311_7436.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___311_7436.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___311_7436.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___311_7436.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___311_7436.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___311_7436.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___311_7436.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___311_7436.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___311_7436.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___311_7436.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___311_7436.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___311_7436.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___311_7436.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___311_7436.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___311_7436.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___311_7436.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___311_7436.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___311_7436.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___311_7436.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___311_7436.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___311_7436.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___311_7436.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___311_7436.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___311_7436.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___311_7436.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___311_7436.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___311_7436.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___311_7436.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___311_7436.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___311_7436.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___311_7436.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___311_7436.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___311_7436.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___311_7436.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___311_7436.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___311_7436.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___311_7436.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___311_7436.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7433
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7459 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____7459)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____7381 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_7565  ->
                                  match uu___0_7565 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7569 = FStar_Util.prefix vars
                                         in
                                      (match uu____7569 with
                                       | (uu____7602,xxv) ->
                                           let xx =
                                             let uu____7641 =
                                               let uu____7642 =
                                                 let uu____7648 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7648,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7642
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7641
                                              in
                                           let uu____7651 =
                                             let uu____7652 =
                                               let uu____7660 =
                                                 let uu____7661 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7662 =
                                                   let uu____7673 =
                                                     let uu____7674 =
                                                       let uu____7679 =
                                                         let uu____7680 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7680
                                                          in
                                                       (vapp, uu____7679)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7674
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7673)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7661 uu____7662
                                                  in
                                               (uu____7660,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7652
                                              in
                                           [uu____7651])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7695 = FStar_Util.prefix vars
                                         in
                                      (match uu____7695 with
                                       | (uu____7728,xxv) ->
                                           let xx =
                                             let uu____7767 =
                                               let uu____7768 =
                                                 let uu____7774 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7774,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7768
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7767
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
                                           let uu____7785 =
                                             let uu____7786 =
                                               let uu____7794 =
                                                 let uu____7795 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7796 =
                                                   let uu____7807 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7807)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7795 uu____7796
                                                  in
                                               (uu____7794,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7786
                                              in
                                           [uu____7785])
                                  | uu____7820 -> []))
                           in
                        let uu____7821 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7821 with
                         | (vars,guards,env',decls1,uu____7846) ->
                             let uu____7859 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7872 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7872, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7876 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7876 with
                                    | (g,ds) ->
                                        let uu____7889 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7889,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7859 with
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
                                  let should_thunk uu____7912 =
                                    let is_type1 t =
                                      let uu____7920 =
                                        let uu____7921 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7921.FStar_Syntax_Syntax.n  in
                                      match uu____7920 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7925 -> true
                                      | uu____7927 -> false  in
                                    let is_squash1 t =
                                      let uu____7936 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____7936 with
                                      | (head1,uu____7955) ->
                                          let uu____7980 =
                                            let uu____7981 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____7981.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7980 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____7986;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____7987;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____7989;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____7990;_};_},uu____7991)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____7999 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____8004 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____8004))
                                       &&
                                       (let uu____8010 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____8010))
                                      &&
                                      (let uu____8013 = is_type1 t_norm  in
                                       Prims.op_Negation uu____8013)
                                     in
                                  let uu____8015 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____8074 -> (false, vars)  in
                                  (match uu____8015 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____8124 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____8124 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____8156 =
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
                                              | uu____8177 ->
                                                  let uu____8186 =
                                                    let uu____8194 =
                                                      get_vtok ()  in
                                                    (uu____8194, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8186
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____8201 =
                                                let uu____8209 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____8209)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____8201
                                               in
                                            let uu____8223 =
                                              let vname_decl =
                                                let uu____8231 =
                                                  let uu____8243 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____8243,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____8231
                                                 in
                                              let uu____8254 =
                                                let env2 =
                                                  let uu___406_8260 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___406_8260.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____8261 =
                                                  let uu____8263 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____8263
                                                   in
                                                if uu____8261
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____8254 with
                                              | (tok_typing,decls2) ->
                                                  let uu____8280 =
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
                                                        let uu____8306 =
                                                          let uu____8309 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8309
                                                           in
                                                        let uu____8316 =
                                                          let uu____8317 =
                                                            let uu____8320 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (vname, [])
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _8326  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _8326)
                                                              uu____8320
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____8317
                                                           in
                                                        (uu____8306,
                                                          uu____8316)
                                                    | uu____8329 when thunked
                                                        -> (decls2, env1)
                                                    | uu____8342 ->
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
                                                          let uu____8366 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____8367 =
                                                            let uu____8378 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____8378)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____8366
                                                            uu____8367
                                                           in
                                                        let name_tok_corr =
                                                          let uu____8388 =
                                                            let uu____8396 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____8396,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8388
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
                                                            let uu____8407 =
                                                              let uu____8408
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8408]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8407
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8435 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8436 =
                                                              let uu____8447
                                                                =
                                                                let uu____8448
                                                                  =
                                                                  let uu____8453
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8454
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8453,
                                                                    uu____8454)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8448
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8447)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8435
                                                              uu____8436
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8483 =
                                                          let uu____8486 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8486
                                                           in
                                                        (uu____8483, env1)
                                                     in
                                                  (match uu____8280 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8507 =
                                                         let uu____8510 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8510
                                                           tok_decl
                                                          in
                                                       (uu____8507, env2))
                                               in
                                            (match uu____8223 with
                                             | (decls2,env2) ->
                                                 let uu____8529 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8539 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8539 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8554 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8554, decls)
                                                    in
                                                 (match uu____8529 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8569 =
                                                          let uu____8577 =
                                                            let uu____8578 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8579 =
                                                              let uu____8590
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8590)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8578
                                                              uu____8579
                                                             in
                                                          (uu____8577,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8569
                                                         in
                                                      let freshness =
                                                        let uu____8606 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8606
                                                        then
                                                          let uu____8614 =
                                                            let uu____8615 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8616 =
                                                              let uu____8629
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8636
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8629,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8636)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8615
                                                              uu____8616
                                                             in
                                                          let uu____8642 =
                                                            let uu____8645 =
                                                              let uu____8646
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8646
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8645]  in
                                                          uu____8614 ::
                                                            uu____8642
                                                        else []  in
                                                      let g =
                                                        let uu____8652 =
                                                          let uu____8655 =
                                                            let uu____8658 =
                                                              let uu____8661
                                                                =
                                                                let uu____8664
                                                                  =
                                                                  let uu____8667
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8667
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8664
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8661
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8658
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8655
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8652
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
          let uu____8707 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8707 with
          | FStar_Pervasives_Native.None  ->
              let uu____8718 = encode_free_var false env x t t_norm []  in
              (match uu____8718 with
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
            let uu____8781 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8781 with
            | (decls,env1) ->
                let uu____8792 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8792
                then
                  let uu____8799 =
                    let uu____8800 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8800  in
                  (uu____8799, env1)
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
             (fun uu____8856  ->
                fun lb  ->
                  match uu____8856 with
                  | (decls,env1) ->
                      let uu____8876 =
                        let uu____8881 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8881
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8876 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8910 = FStar_Syntax_Util.head_and_args t  in
    match uu____8910 with
    | (hd1,args) ->
        let uu____8954 =
          let uu____8955 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8955.FStar_Syntax_Syntax.n  in
        (match uu____8954 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8961,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____8985 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____8996 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___490_9004 = en  in
    let uu____9005 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___490_9004.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___490_9004.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___490_9004.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___490_9004.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___490_9004.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___490_9004.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___490_9004.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___490_9004.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___490_9004.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___490_9004.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____9005
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____9035  ->
      fun quals  ->
        match uu____9035 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____9140 = FStar_Util.first_N nbinders formals  in
              match uu____9140 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____9237  ->
                         fun uu____9238  ->
                           match (uu____9237, uu____9238) with
                           | ((formal,uu____9264),(binder,uu____9266)) ->
                               let uu____9287 =
                                 let uu____9294 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____9294)  in
                               FStar_Syntax_Syntax.NT uu____9287) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____9308 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____9349  ->
                              match uu____9349 with
                              | (x,i) ->
                                  let uu____9368 =
                                    let uu___516_9369 = x  in
                                    let uu____9370 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___516_9369.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___516_9369.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9370
                                    }  in
                                  (uu____9368, i)))
                       in
                    FStar_All.pipe_right uu____9308
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9394 =
                      let uu____9399 = FStar_Syntax_Subst.compress body  in
                      let uu____9400 =
                        let uu____9401 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9401
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____9399 uu____9400
                       in
                    uu____9394 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___523_9450 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___523_9450.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___523_9450.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___523_9450.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___523_9450.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___523_9450.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___523_9450.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___523_9450.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___523_9450.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___523_9450.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___523_9450.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___523_9450.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___523_9450.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___523_9450.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___523_9450.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___523_9450.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___523_9450.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___523_9450.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___523_9450.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___523_9450.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___523_9450.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___523_9450.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___523_9450.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___523_9450.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___523_9450.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___523_9450.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___523_9450.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___523_9450.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___523_9450.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___523_9450.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___523_9450.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___523_9450.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___523_9450.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___523_9450.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___523_9450.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___523_9450.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___523_9450.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___523_9450.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___523_9450.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___523_9450.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___523_9450.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___523_9450.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___523_9450.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____9522  ->
                       fun uu____9523  ->
                         match (uu____9522, uu____9523) with
                         | ((x,uu____9549),(b,uu____9551)) ->
                             let uu____9572 =
                               let uu____9579 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9579)  in
                             FStar_Syntax_Syntax.NT uu____9572) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9604 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9604
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9633 ->
                    let uu____9640 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9640
                | uu____9641 when Prims.op_Negation norm1 ->
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
                | uu____9644 ->
                    let uu____9645 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9645)
                 in
              let aux t1 e1 =
                let uu____9687 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9687 with
                | (binders,body,lopt) ->
                    let uu____9719 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9735 -> arrow_formals_comp_norm false t1  in
                    (match uu____9719 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9769 =
                           if nformals < nbinders
                           then
                             let uu____9803 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9803 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9883 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9883)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9913 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9913 with
                                | (binders1,body1) ->
                                    let uu____9966 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____9966))
                             else
                               (let uu____9979 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____9979))
                            in
                         (match uu____9769 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____10039 = aux t e  in
              match uu____10039 with
              | (binders,body,comp) ->
                  let uu____10085 =
                    let uu____10096 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____10096
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____10111 = aux comp1 body1  in
                      match uu____10111 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____10085 with
                   | (binders1,body1,comp1) ->
                       let uu____10194 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____10194, comp1))
               in
            (try
               (fun uu___593_10221  ->
                  match () with
                  | () ->
                      let uu____10228 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____10228
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____10244 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____10307  ->
                                   fun lb  ->
                                     match uu____10307 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____10362 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____10362
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____10368 =
                                             let uu____10377 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____10377
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____10368 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____10244 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10518;
                                    FStar_Syntax_Syntax.lbeff = uu____10519;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10521;
                                    FStar_Syntax_Syntax.lbpos = uu____10522;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10546 =
                                     let uu____10553 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10553 with
                                     | (tcenv',uu____10569,e_t) ->
                                         let uu____10575 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10586 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10575 with
                                          | (e1,t_norm1) ->
                                              ((let uu___656_10603 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___656_10603.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10546 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10613 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10613 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10633 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10633
                                               then
                                                 let uu____10638 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10641 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10638 uu____10641
                                               else ());
                                              (let uu____10646 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10646 with
                                               | (vars,_guards,env'1,binder_decls,uu____10673)
                                                   ->
                                                   let uu____10686 =
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
                                                         let uu____10703 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10703
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10725 =
                                                          let uu____10726 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10727 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10726 fvb
                                                            uu____10727
                                                           in
                                                        (vars, uu____10725))
                                                      in
                                                   (match uu____10686 with
                                                    | (vars1,app) ->
                                                        let uu____10738 =
                                                          let is_logical =
                                                            let uu____10751 =
                                                              let uu____10752
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10752.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10751
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10758 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10762 =
                                                              let uu____10763
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10763
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10762
                                                              (fun lid  ->
                                                                 let uu____10772
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10772
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10773 =
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
                                                          if uu____10773
                                                          then
                                                            let uu____10789 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10790 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10789,
                                                              uu____10790)
                                                          else
                                                            (let uu____10801
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10801))
                                                           in
                                                        (match uu____10738
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10825
                                                                 =
                                                                 let uu____10833
                                                                   =
                                                                   let uu____10834
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10835
                                                                    =
                                                                    let uu____10846
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10846)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10834
                                                                    uu____10835
                                                                    in
                                                                 let uu____10855
                                                                   =
                                                                   let uu____10856
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10856
                                                                    in
                                                                 (uu____10833,
                                                                   uu____10855,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10825
                                                                in
                                                             let uu____10862
                                                               =
                                                               let uu____10865
                                                                 =
                                                                 let uu____10868
                                                                   =
                                                                   let uu____10871
                                                                    =
                                                                    let uu____10874
                                                                    =
                                                                    let uu____10877
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10877
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10874
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10871
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10868
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10865
                                                                in
                                                             (uu____10862,
                                                               env2)))))))
                               | uu____10886 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10946 =
                                   let uu____10952 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____10952,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10946  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10958 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____11011  ->
                                         fun fvb  ->
                                           match uu____11011 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____11066 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11066
                                                  in
                                               let gtok =
                                                 let uu____11070 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11070
                                                  in
                                               let env4 =
                                                 let uu____11073 =
                                                   let uu____11076 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _11082  ->
                                                        FStar_Pervasives_Native.Some
                                                          _11082) uu____11076
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____11073
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10958 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____11202
                                     t_norm uu____11204 =
                                     match (uu____11202, uu____11204) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____11234;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____11235;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____11237;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____11238;_})
                                         ->
                                         let uu____11265 =
                                           let uu____11272 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____11272 with
                                           | (tcenv',uu____11288,e_t) ->
                                               let uu____11294 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____11305 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____11294 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___743_11322 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___743_11322.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____11265 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____11335 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____11335
                                                then
                                                  let uu____11340 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____11342 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____11344 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____11340 uu____11342
                                                    uu____11344
                                                else ());
                                               (let uu____11349 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____11349 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____11376 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____11376 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11398 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11398
                                                           then
                                                             let uu____11403
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11405
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11408
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11410
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11403
                                                               uu____11405
                                                               uu____11408
                                                               uu____11410
                                                           else ());
                                                          (let uu____11415 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11415
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11444)
                                                               ->
                                                               let uu____11457
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11470
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11470,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11474
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11474
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11487
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11487,
                                                                    decls0))
                                                                  in
                                                               (match uu____11457
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
                                                                    let uu____11508
                                                                    =
                                                                    let uu____11520
                                                                    =
                                                                    let uu____11523
                                                                    =
                                                                    let uu____11526
                                                                    =
                                                                    let uu____11529
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11529
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11526
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11523
                                                                     in
                                                                    (g,
                                                                    uu____11520,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11508
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
                                                                    let uu____11559
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11559
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
                                                                    let uu____11574
                                                                    =
                                                                    let uu____11577
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11577
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11574
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11583
                                                                    =
                                                                    let uu____11586
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11586
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11583
                                                                     in
                                                                    let uu____11591
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11591
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11607
                                                                    =
                                                                    let uu____11615
                                                                    =
                                                                    let uu____11616
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11617
                                                                    =
                                                                    let uu____11633
                                                                    =
                                                                    let uu____11634
                                                                    =
                                                                    let uu____11639
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11639)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11634
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11633)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11616
                                                                    uu____11617
                                                                     in
                                                                    let uu____11653
                                                                    =
                                                                    let uu____11654
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11654
                                                                     in
                                                                    (uu____11615,
                                                                    uu____11653,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11607
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11661
                                                                    =
                                                                    let uu____11669
                                                                    =
                                                                    let uu____11670
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11671
                                                                    =
                                                                    let uu____11682
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11682)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11670
                                                                    uu____11671
                                                                     in
                                                                    (uu____11669,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11661
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11696
                                                                    =
                                                                    let uu____11704
                                                                    =
                                                                    let uu____11705
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11706
                                                                    =
                                                                    let uu____11717
                                                                    =
                                                                    let uu____11718
                                                                    =
                                                                    let uu____11723
                                                                    =
                                                                    let uu____11724
                                                                    =
                                                                    let uu____11727
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11727
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11724
                                                                     in
                                                                    (gsapp,
                                                                    uu____11723)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11718
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11717)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11705
                                                                    uu____11706
                                                                     in
                                                                    (uu____11704,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11696
                                                                     in
                                                                    let uu____11741
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
                                                                    let uu____11753
                                                                    =
                                                                    let uu____11754
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11754
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11753
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head1
                                                                    =
                                                                    let uu____11758
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11758
                                                                     in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars  in
                                                                    let guards1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11767
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue)
                                                                    vars1  in
                                                                    let uu____11768
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_comp
                                                                    tres_comp
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head1
                                                                    vars1
                                                                    guards1
                                                                    uu____11768
                                                                     in
                                                                    let uu____11770
                                                                    =
                                                                    let uu____11778
                                                                    =
                                                                    let uu____11779
                                                                    =
                                                                    let uu____11784
                                                                    =
                                                                    let uu____11785
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11786
                                                                    =
                                                                    let uu____11797
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11797)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11785
                                                                    uu____11786
                                                                     in
                                                                    (uu____11784,
                                                                    tot_fun_axioms)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____11779
                                                                     in
                                                                    (uu____11778,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11770
                                                                     in
                                                                    let uu____11810
                                                                    =
                                                                    let uu____11819
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11819
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11834
                                                                    =
                                                                    let uu____11837
                                                                    =
                                                                    let uu____11838
                                                                    =
                                                                    let uu____11846
                                                                    =
                                                                    let uu____11847
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11848
                                                                    =
                                                                    let uu____11859
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11859)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11847
                                                                    uu____11848
                                                                     in
                                                                    (uu____11846,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11838
                                                                     in
                                                                    [uu____11837]
                                                                     in
                                                                    (d3,
                                                                    uu____11834)
                                                                     in
                                                                    match uu____11810
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11741
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11916
                                                                    =
                                                                    let uu____11919
                                                                    =
                                                                    let uu____11922
                                                                    =
                                                                    let uu____11925
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11925
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11922
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11919
                                                                     in
                                                                    let uu____11932
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11916,
                                                                    uu____11932,
                                                                    env02))))))))))
                                      in
                                   let uu____11937 =
                                     let uu____11950 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____12013  ->
                                          fun uu____12014  ->
                                            match (uu____12013, uu____12014)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____12139 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____12139 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11950
                                      in
                                   (match uu____11937 with
                                    | (decls2,eqns,env01) ->
                                        let uu____12206 =
                                          let isDeclFun uu___1_12223 =
                                            match uu___1_12223 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____12225 -> true
                                            | uu____12238 -> false  in
                                          let uu____12240 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____12240
                                            (fun decls3  ->
                                               let uu____12270 =
                                                 FStar_List.fold_left
                                                   (fun uu____12301  ->
                                                      fun elt  ->
                                                        match uu____12301
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____12342 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____12342
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____12370
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____12370
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
                                                                    let uu___841_12408
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___841_12408.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___841_12408.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___841_12408.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____12270 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12440 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12440, elts, rest))
                                           in
                                        (match uu____12206 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12469 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12475  ->
                                        match uu___2_12475 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12478 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12486 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12486)))
                                in
                             if uu____12469
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___858_12508  ->
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
                                | FStar_SMTEncoding_Env.Inner_let_rec 
                                    (s,r) ->
                                    ((let uu____12540 =
                                        let uu____12550 =
                                          let uu____12558 =
                                            FStar_Util.format1
                                              "Definitions of inner let-rec %s and its enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types"
                                              s
                                             in
                                          (FStar_Errors.Warning_DefinitionNotTranslated,
                                            uu____12558, r)
                                           in
                                        [uu____12550]  in
                                      FStar_TypeChecker_Err.add_errors
                                        env1.FStar_SMTEncoding_Env.tcenv
                                        uu____12540);
                                     (decls1, env_decls))))) ()
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12591 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12591
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12610 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12610, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12666 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12666 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12672 = encode_sigelt' env se  in
      match uu____12672 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12684 =
                  let uu____12687 =
                    let uu____12688 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12688  in
                  [uu____12687]  in
                FStar_All.pipe_right uu____12684
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12693 ->
                let uu____12694 =
                  let uu____12697 =
                    let uu____12700 =
                      let uu____12701 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12701  in
                    [uu____12700]  in
                  FStar_All.pipe_right uu____12697
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12708 =
                  let uu____12711 =
                    let uu____12714 =
                      let uu____12717 =
                        let uu____12718 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12718  in
                      [uu____12717]  in
                    FStar_All.pipe_right uu____12714
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12711  in
                FStar_List.append uu____12694 uu____12708
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12732 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12732
       then
         let uu____12737 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12737
       else ());
      (let is_opaque_to_smt t =
         let uu____12749 =
           let uu____12750 = FStar_Syntax_Subst.compress t  in
           uu____12750.FStar_Syntax_Syntax.n  in
         match uu____12749 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12755)) -> s = "opaque_to_smt"
         | uu____12760 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12769 =
           let uu____12770 = FStar_Syntax_Subst.compress t  in
           uu____12770.FStar_Syntax_Syntax.n  in
         match uu____12769 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12775)) -> s = "uninterpreted_by_smt"
         | uu____12780 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12786 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12792 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12804 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12805 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12806 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12819 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12821 =
             let uu____12823 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12823  in
           if uu____12821
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12852 ->
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
                  let uu____12885 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____12885  in
                let uu____12886 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12886 with
                | (formals,uu____12906) ->
                    let arity = FStar_List.length formals  in
                    let uu____12930 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12930 with
                     | (aname,atok,env2) ->
                         let uu____12952 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____12952 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12968 =
                                  let uu____12969 =
                                    let uu____12981 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____13001  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12981,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12969
                                   in
                                [uu____12968;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____13018 =
                                let aux uu____13064 uu____13065 =
                                  match (uu____13064, uu____13065) with
                                  | ((bv,uu____13109),(env3,acc_sorts,acc))
                                      ->
                                      let uu____13141 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____13141 with
                                       | (xxsym,xx,env4) ->
                                           let uu____13164 =
                                             let uu____13167 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____13167 :: acc_sorts  in
                                           (env4, uu____13164, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____13018 with
                               | (uu____13199,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____13215 =
                                       let uu____13223 =
                                         let uu____13224 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13225 =
                                           let uu____13236 =
                                             let uu____13237 =
                                               let uu____13242 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____13242)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____13237
                                              in
                                           ([[app]], xs_sorts, uu____13236)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13224 uu____13225
                                          in
                                       (uu____13223,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13215
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____13257 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____13257
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____13260 =
                                       let uu____13268 =
                                         let uu____13269 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13270 =
                                           let uu____13281 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____13281)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13269 uu____13270
                                          in
                                       (uu____13268,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13260
                                      in
                                   let uu____13294 =
                                     let uu____13297 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____13297  in
                                   (env2, uu____13294))))
                 in
              let uu____13306 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____13306 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13332,uu____13333)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____13334 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____13334 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13356,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____13363 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_13369  ->
                       match uu___3_13369 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____13372 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____13378 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____13381 -> false))
                in
             Prims.op_Negation uu____13363  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____13391 =
                let uu____13396 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____13396 env fv t quals  in
              match uu____13391 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____13410 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____13410  in
                  let uu____13413 =
                    let uu____13414 =
                      let uu____13417 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____13417
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____13414  in
                  (uu____13413, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13427 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13427 with
            | (uvs,f1) ->
                let env1 =
                  let uu___999_13439 = env  in
                  let uu____13440 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___999_13439.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___999_13439.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___999_13439.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13440;
                    FStar_SMTEncoding_Env.warn =
                      (uu___999_13439.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___999_13439.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___999_13439.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___999_13439.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___999_13439.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___999_13439.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___999_13439.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____13442 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13442 with
                 | (f3,decls) ->
                     let g =
                       let uu____13456 =
                         let uu____13459 =
                           let uu____13460 =
                             let uu____13468 =
                               let uu____13469 =
                                 let uu____13471 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13471
                                  in
                               FStar_Pervasives_Native.Some uu____13469  in
                             let uu____13475 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13468, uu____13475)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13460  in
                         [uu____13459]  in
                       FStar_All.pipe_right uu____13456
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13484) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13498 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13520 =
                        let uu____13523 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13523.FStar_Syntax_Syntax.fv_name  in
                      uu____13520.FStar_Syntax_Syntax.v  in
                    let uu____13524 =
                      let uu____13526 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13526  in
                    if uu____13524
                    then
                      let val_decl =
                        let uu___1016_13558 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1016_13558.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1016_13558.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1016_13558.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____13559 = encode_sigelt' env1 val_decl  in
                      match uu____13559 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13498 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13595,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13597;
                           FStar_Syntax_Syntax.lbtyp = uu____13598;
                           FStar_Syntax_Syntax.lbeff = uu____13599;
                           FStar_Syntax_Syntax.lbdef = uu____13600;
                           FStar_Syntax_Syntax.lbattrs = uu____13601;
                           FStar_Syntax_Syntax.lbpos = uu____13602;_}::[]),uu____13603)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13622 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____13622 with
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
                  let uu____13660 =
                    let uu____13663 =
                      let uu____13664 =
                        let uu____13672 =
                          let uu____13673 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13674 =
                            let uu____13685 =
                              let uu____13686 =
                                let uu____13691 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13691)  in
                              FStar_SMTEncoding_Util.mkEq uu____13686  in
                            ([[b2t_x]], [xx], uu____13685)  in
                          FStar_SMTEncoding_Term.mkForall uu____13673
                            uu____13674
                           in
                        (uu____13672,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13664  in
                    [uu____13663]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13660
                   in
                let uu____13729 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13729, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13732,uu____13733) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13743  ->
                   match uu___4_13743 with
                   | FStar_Syntax_Syntax.Discriminator uu____13745 -> true
                   | uu____13747 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13749,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13761 =
                      let uu____13763 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13763.FStar_Ident.idText  in
                    uu____13761 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13770  ->
                      match uu___5_13770 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13773 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13776) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13790  ->
                   match uu___6_13790 with
                   | FStar_Syntax_Syntax.Projector uu____13792 -> true
                   | uu____13798 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13802 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13802 with
            | FStar_Pervasives_Native.Some uu____13809 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1081_13811 = se  in
                  let uu____13812 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13812;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1081_13811.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1081_13811.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1081_13811.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13815) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1093_13836 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1093_13836.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1093_13836.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1093_13836.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1093_13836.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1093_13836.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13841) ->
           let uu____13850 = encode_sigelts env ses  in
           (match uu____13850 with
            | (g,env1) ->
                let uu____13861 =
                  FStar_List.fold_left
                    (fun uu____13885  ->
                       fun elt  ->
                         match uu____13885 with
                         | (g',inversions) ->
                             let uu____13913 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_13936  ->
                                       match uu___7_13936 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13938;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13939;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13940;_}
                                           -> false
                                       | uu____13947 -> true))
                                in
                             (match uu____13913 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1119_13972 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1119_13972.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1119_13972.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1119_13972.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13861 with
                 | (g',inversions) ->
                     let uu____13991 =
                       FStar_List.fold_left
                         (fun uu____14022  ->
                            fun elt  ->
                              match uu____14022 with
                              | (decls,elts,rest) ->
                                  let uu____14063 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_14072  ->
                                            match uu___8_14072 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____14074 -> true
                                            | uu____14087 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____14063
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____14110 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_14131  ->
                                               match uu___9_14131 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____14133 -> true
                                               | uu____14146 -> false))
                                        in
                                     match uu____14110 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1141_14177 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1141_14177.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1141_14177.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1141_14177.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____13991 with
                      | (decls,elts,rest) ->
                          let uu____14203 =
                            let uu____14204 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____14211 =
                              let uu____14214 =
                                let uu____14217 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____14217  in
                              FStar_List.append elts uu____14214  in
                            FStar_List.append uu____14204 uu____14211  in
                          (uu____14203, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____14228,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____14241 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____14241 with
             | (usubst,uvs) ->
                 let uu____14261 =
                   let uu____14268 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____14269 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____14270 =
                     let uu____14271 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____14271 k  in
                   (uu____14268, uu____14269, uu____14270)  in
                 (match uu____14261 with
                  | (env1,tps1,k1) ->
                      let uu____14284 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____14284 with
                       | (tps2,k2) ->
                           let uu____14292 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____14292 with
                            | (uu____14308,k3) ->
                                let uu____14330 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____14330 with
                                 | (tps3,env_tps,uu____14342,us) ->
                                     let u_k =
                                       let uu____14345 =
                                         let uu____14346 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14347 =
                                           let uu____14352 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____14354 =
                                             let uu____14355 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____14355
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____14352 uu____14354
                                            in
                                         uu____14347
                                           FStar_Pervasives_Native.None
                                           uu____14346
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____14345 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____14373) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____14379,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____14382) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____14390,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____14397) ->
                                           let uu____14398 =
                                             let uu____14400 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14400
                                              in
                                           failwith uu____14398
                                       | (uu____14404,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____14405 =
                                             let uu____14407 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14407
                                              in
                                           failwith uu____14405
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14411,uu____14412) ->
                                           let uu____14421 =
                                             let uu____14423 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14423
                                              in
                                           failwith uu____14421
                                       | (uu____14427,FStar_Syntax_Syntax.U_unif
                                          uu____14428) ->
                                           let uu____14437 =
                                             let uu____14439 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14439
                                              in
                                           failwith uu____14437
                                       | uu____14443 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14456 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14456 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14474 = u_leq_u_k u_tp  in
                                       if uu____14474
                                       then true
                                       else
                                         (let uu____14481 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14481 with
                                          | (formals,uu____14498) ->
                                              let uu____14519 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14519 with
                                               | (uu____14529,uu____14530,uu____14531,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14542 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14542
             then
               let uu____14547 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14547
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14567  ->
                       match uu___10_14567 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14571 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14584 = c  in
                 match uu____14584 with
                 | (name,args,uu____14589,uu____14590,uu____14591) ->
                     let uu____14602 =
                       let uu____14603 =
                         let uu____14615 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14642  ->
                                   match uu____14642 with
                                   | (uu____14651,sort,uu____14653) -> sort))
                            in
                         (name, uu____14615,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14603  in
                     [uu____14602]
               else
                 (let uu____14664 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14664 c)
                in
             let inversion_axioms tapp vars =
               let uu____14682 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14690 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14690 FStar_Option.isNone))
                  in
               if uu____14682
               then []
               else
                 (let uu____14725 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14725 with
                  | (xxsym,xx) ->
                      let uu____14738 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14777  ->
                                fun l  ->
                                  match uu____14777 with
                                  | (out,decls) ->
                                      let uu____14797 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14797 with
                                       | (uu____14808,data_t) ->
                                           let uu____14810 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14810 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14854 =
                                                    let uu____14855 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14855.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14854 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14858,indices)
                                                      -> indices
                                                  | uu____14884 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14914  ->
                                                            match uu____14914
                                                            with
                                                            | (x,uu____14922)
                                                                ->
                                                                let uu____14927
                                                                  =
                                                                  let uu____14928
                                                                    =
                                                                    let uu____14936
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14936,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14928
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14927)
                                                       env)
                                                   in
                                                let uu____14941 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14941 with
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
                                                                  let uu____14976
                                                                    =
                                                                    let uu____14981
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____14981,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____14976)
                                                             vars indices1
                                                         else []  in
                                                       let uu____14984 =
                                                         let uu____14985 =
                                                           let uu____14990 =
                                                             let uu____14991
                                                               =
                                                               let uu____14996
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____14997
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____14996,
                                                                 uu____14997)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____14991
                                                              in
                                                           (out, uu____14990)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____14985
                                                          in
                                                       (uu____14984,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14738 with
                       | (data_ax,decls) ->
                           let uu____15012 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____15012 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____15029 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____15029 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____15036 =
                                    let uu____15044 =
                                      let uu____15045 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____15046 =
                                        let uu____15057 =
                                          let uu____15058 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____15060 =
                                            let uu____15063 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____15063 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____15058 uu____15060
                                           in
                                        let uu____15065 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____15057,
                                          uu____15065)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____15045 uu____15046
                                       in
                                    let uu____15074 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____15044,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____15074)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____15036
                                   in
                                let uu____15080 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____15080)))
                in
             let uu____15087 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____15109 ->
                     let uu____15110 =
                       let uu____15117 =
                         let uu____15118 =
                           let uu____15133 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____15133)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____15118  in
                       FStar_Syntax_Syntax.mk uu____15117  in
                     uu____15110 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____15087 with
             | (formals,res) ->
                 let uu____15173 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____15173 with
                  | (vars,guards,env',binder_decls,uu____15198) ->
                      let arity = FStar_List.length vars  in
                      let uu____15212 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____15212 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____15238 =
                               let uu____15246 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____15246)  in
                             FStar_SMTEncoding_Util.mkApp uu____15238  in
                           let uu____15252 =
                             let tname_decl =
                               let uu____15262 =
                                 let uu____15263 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____15282 =
                                             let uu____15284 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____15284
                                              in
                                           let uu____15286 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____15282, uu____15286, false)))
                                    in
                                 let uu____15290 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____15263,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____15290, false)
                                  in
                               constructor_or_logic_type_decl uu____15262  in
                             let uu____15298 =
                               match vars with
                               | [] ->
                                   let uu____15311 =
                                     let uu____15312 =
                                       let uu____15315 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _15321  ->
                                            FStar_Pervasives_Native.Some
                                              _15321) uu____15315
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____15312
                                      in
                                   ([], uu____15311)
                               | uu____15324 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____15334 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____15334
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____15350 =
                                       let uu____15358 =
                                         let uu____15359 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____15360 =
                                           let uu____15376 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____15376)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____15359 uu____15360
                                          in
                                       (uu____15358,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____15350
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____15298 with
                             | (tok_decls,env2) ->
                                 let uu____15403 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____15403
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____15252 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____15431 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____15431 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____15453 =
                                            let uu____15454 =
                                              let uu____15462 =
                                                let uu____15463 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15463
                                                 in
                                              (uu____15462,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15454
                                             in
                                          [uu____15453]
                                        else []  in
                                      let rng = FStar_Ident.range_of_lid t
                                         in
                                      let tot_fun_axioms =
                                        let uu____15473 =
                                          FStar_List.map
                                            (fun uu____15477  ->
                                               FStar_SMTEncoding_Util.mkTrue)
                                            vars
                                           in
                                        FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                          rng ttok_tm vars uu____15473 true
                                         in
                                      let uu____15479 =
                                        let uu____15482 =
                                          let uu____15485 =
                                            let uu____15488 =
                                              let uu____15489 =
                                                let uu____15497 =
                                                  let uu____15498 =
                                                    let uu____15503 =
                                                      let uu____15504 =
                                                        let uu____15515 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1)
                                                           in
                                                        ([[tapp]], vars,
                                                          uu____15515)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        rng uu____15504
                                                       in
                                                    (tot_fun_axioms,
                                                      uu____15503)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15498
                                                   in
                                                (uu____15497,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15489
                                               in
                                            [uu____15488]  in
                                          FStar_List.append karr uu____15485
                                           in
                                        FStar_All.pipe_right uu____15482
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15479
                                   in
                                let aux =
                                  let uu____15534 =
                                    let uu____15537 =
                                      inversion_axioms tapp vars  in
                                    let uu____15540 =
                                      let uu____15543 =
                                        let uu____15546 =
                                          let uu____15547 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15547 env2 tapp
                                            vars
                                           in
                                        [uu____15546]  in
                                      FStar_All.pipe_right uu____15543
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15537 uu____15540
                                     in
                                  FStar_List.append kindingAx uu____15534  in
                                let g =
                                  let uu____15555 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15555
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15563,uu____15564,uu____15565,uu____15566,uu____15567)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15575,t,uu____15577,n_tps,uu____15579) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15590 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15590 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15638 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15638 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15662 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15662 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15682 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15682 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15761 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15761,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15768 =
                                   let uu____15769 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15769, true)
                                    in
                                 let uu____15777 =
                                   let uu____15784 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15784
                                    in
                                 FStar_All.pipe_right uu____15768 uu____15777
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
                               let uu____15796 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15796 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15808::uu____15809 ->
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
                                            let uu____15858 =
                                              let uu____15859 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15859]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15858
                                             in
                                          let uu____15885 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15886 =
                                            let uu____15897 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15897)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15885 uu____15886
                                      | uu____15924 -> tok_typing  in
                                    let uu____15935 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15935 with
                                     | (vars',guards',env'',decls_formals,uu____15960)
                                         ->
                                         let uu____15973 =
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
                                         (match uu____15973 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____16003 ->
                                                    let uu____16012 =
                                                      let uu____16013 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____16013
                                                       in
                                                    [uu____16012]
                                                 in
                                              let encode_elim uu____16029 =
                                                let uu____16030 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____16030 with
                                                | (head1,args) ->
                                                    let uu____16081 =
                                                      let uu____16082 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____16082.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____16081 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____16094;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____16095;_},uu____16096)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____16102 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16102
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
                                                                  | uu____16165
                                                                    ->
                                                                    let uu____16166
                                                                    =
                                                                    let uu____16172
                                                                    =
                                                                    let uu____16174
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16174
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16172)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16166
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16197
                                                                    =
                                                                    let uu____16199
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16199
                                                                     in
                                                                    if
                                                                    uu____16197
                                                                    then
                                                                    let uu____16221
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16221]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16224
                                                                =
                                                                let uu____16238
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16295
                                                                     ->
                                                                    fun
                                                                    uu____16296
                                                                     ->
                                                                    match 
                                                                    (uu____16295,
                                                                    uu____16296)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16407
                                                                    =
                                                                    let uu____16415
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16415
                                                                     in
                                                                    (match uu____16407
                                                                    with
                                                                    | 
                                                                    (uu____16429,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16440
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16440
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16445
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16445
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
                                                                  uu____16238
                                                                 in
                                                              (match uu____16224
                                                               with
                                                               | (uu____16466,arg_vars,elim_eqns_or_guards,uu____16469)
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
                                                                    let uu____16496
                                                                    =
                                                                    let uu____16504
                                                                    =
                                                                    let uu____16505
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16506
                                                                    =
                                                                    let uu____16517
                                                                    =
                                                                    let uu____16518
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16518
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16520
                                                                    =
                                                                    let uu____16521
                                                                    =
                                                                    let uu____16526
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16526)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16521
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16517,
                                                                    uu____16520)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16505
                                                                    uu____16506
                                                                     in
                                                                    (uu____16504,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16496
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16541
                                                                    =
                                                                    let uu____16542
                                                                    =
                                                                    let uu____16548
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16548,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16542
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16541
                                                                     in
                                                                    let uu____16551
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16551
                                                                    then
                                                                    let x =
                                                                    let uu____16555
                                                                    =
                                                                    let uu____16561
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16561,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16555
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16566
                                                                    =
                                                                    let uu____16574
                                                                    =
                                                                    let uu____16575
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16576
                                                                    =
                                                                    let uu____16587
                                                                    =
                                                                    let uu____16592
                                                                    =
                                                                    let uu____16595
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16595]
                                                                     in
                                                                    [uu____16592]
                                                                     in
                                                                    let uu____16600
                                                                    =
                                                                    let uu____16601
                                                                    =
                                                                    let uu____16606
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16608
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16606,
                                                                    uu____16608)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16601
                                                                     in
                                                                    (uu____16587,
                                                                    [x],
                                                                    uu____16600)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16575
                                                                    uu____16576
                                                                     in
                                                                    let uu____16629
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16574,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16629)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16566
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16640
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
                                                                    (let uu____16663
                                                                    =
                                                                    let uu____16664
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16664
                                                                    dapp1  in
                                                                    [uu____16663])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16640
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16671
                                                                    =
                                                                    let uu____16679
                                                                    =
                                                                    let uu____16680
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16681
                                                                    =
                                                                    let uu____16692
                                                                    =
                                                                    let uu____16693
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16693
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16695
                                                                    =
                                                                    let uu____16696
                                                                    =
                                                                    let uu____16701
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16701)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16696
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16692,
                                                                    uu____16695)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16680
                                                                    uu____16681
                                                                     in
                                                                    (uu____16679,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16671)
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
                                                         let uu____16720 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16720
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
                                                                  | uu____16783
                                                                    ->
                                                                    let uu____16784
                                                                    =
                                                                    let uu____16790
                                                                    =
                                                                    let uu____16792
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16792
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16790)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16784
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16815
                                                                    =
                                                                    let uu____16817
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16817
                                                                     in
                                                                    if
                                                                    uu____16815
                                                                    then
                                                                    let uu____16839
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16839]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16842
                                                                =
                                                                let uu____16856
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16913
                                                                     ->
                                                                    fun
                                                                    uu____16914
                                                                     ->
                                                                    match 
                                                                    (uu____16913,
                                                                    uu____16914)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____17025
                                                                    =
                                                                    let uu____17033
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____17033
                                                                     in
                                                                    (match uu____17025
                                                                    with
                                                                    | 
                                                                    (uu____17047,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____17058
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____17058
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____17063
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____17063
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
                                                                  uu____16856
                                                                 in
                                                              (match uu____16842
                                                               with
                                                               | (uu____17084,arg_vars,elim_eqns_or_guards,uu____17087)
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
                                                                    let uu____17114
                                                                    =
                                                                    let uu____17122
                                                                    =
                                                                    let uu____17123
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17124
                                                                    =
                                                                    let uu____17135
                                                                    =
                                                                    let uu____17136
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17136
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17138
                                                                    =
                                                                    let uu____17139
                                                                    =
                                                                    let uu____17144
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____17144)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17139
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17135,
                                                                    uu____17138)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17123
                                                                    uu____17124
                                                                     in
                                                                    (uu____17122,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17114
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____17159
                                                                    =
                                                                    let uu____17160
                                                                    =
                                                                    let uu____17166
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____17166,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17160
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17159
                                                                     in
                                                                    let uu____17169
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____17169
                                                                    then
                                                                    let x =
                                                                    let uu____17173
                                                                    =
                                                                    let uu____17179
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____17179,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17173
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____17184
                                                                    =
                                                                    let uu____17192
                                                                    =
                                                                    let uu____17193
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17194
                                                                    =
                                                                    let uu____17205
                                                                    =
                                                                    let uu____17210
                                                                    =
                                                                    let uu____17213
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____17213]
                                                                     in
                                                                    [uu____17210]
                                                                     in
                                                                    let uu____17218
                                                                    =
                                                                    let uu____17219
                                                                    =
                                                                    let uu____17224
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____17226
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____17224,
                                                                    uu____17226)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17219
                                                                     in
                                                                    (uu____17205,
                                                                    [x],
                                                                    uu____17218)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17193
                                                                    uu____17194
                                                                     in
                                                                    let uu____17247
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____17192,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____17247)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17184
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____17258
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
                                                                    (let uu____17281
                                                                    =
                                                                    let uu____17282
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____17282
                                                                    dapp1  in
                                                                    [uu____17281])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17258
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____17289
                                                                    =
                                                                    let uu____17297
                                                                    =
                                                                    let uu____17298
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17299
                                                                    =
                                                                    let uu____17310
                                                                    =
                                                                    let uu____17311
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17311
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17313
                                                                    =
                                                                    let uu____17314
                                                                    =
                                                                    let uu____17319
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____17319)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17314
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17310,
                                                                    uu____17313)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17298
                                                                    uu____17299
                                                                     in
                                                                    (uu____17297,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17289)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____17336 ->
                                                         ((let uu____17338 =
                                                             let uu____17344
                                                               =
                                                               let uu____17346
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____17348
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____17346
                                                                 uu____17348
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____17344)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____17338);
                                                          ([], [])))
                                                 in
                                              let uu____17356 =
                                                encode_elim ()  in
                                              (match uu____17356 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____17382 =
                                                       let uu____17385 =
                                                         let uu____17388 =
                                                           let uu____17391 =
                                                             let uu____17394
                                                               =
                                                               let uu____17397
                                                                 =
                                                                 let uu____17400
                                                                   =
                                                                   let uu____17401
                                                                    =
                                                                    let uu____17413
                                                                    =
                                                                    let uu____17414
                                                                    =
                                                                    let uu____17416
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____17416
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____17414
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____17413)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____17401
                                                                    in
                                                                 [uu____17400]
                                                                  in
                                                               FStar_List.append
                                                                 uu____17397
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____17394
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____17427 =
                                                             let uu____17430
                                                               =
                                                               let uu____17433
                                                                 =
                                                                 let uu____17436
                                                                   =
                                                                   let uu____17439
                                                                    =
                                                                    let uu____17442
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____17447
                                                                    =
                                                                    let uu____17450
                                                                    =
                                                                    let uu____17451
                                                                    =
                                                                    let uu____17459
                                                                    =
                                                                    let uu____17460
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17461
                                                                    =
                                                                    let uu____17472
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____17472)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17460
                                                                    uu____17461
                                                                     in
                                                                    (uu____17459,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17451
                                                                     in
                                                                    let uu____17485
                                                                    =
                                                                    let uu____17488
                                                                    =
                                                                    let uu____17489
                                                                    =
                                                                    let uu____17497
                                                                    =
                                                                    let uu____17498
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17499
                                                                    =
                                                                    let uu____17510
                                                                    =
                                                                    let uu____17511
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17511
                                                                    vars'  in
                                                                    let uu____17513
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17510,
                                                                    uu____17513)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17498
                                                                    uu____17499
                                                                     in
                                                                    (uu____17497,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17489
                                                                     in
                                                                    [uu____17488]
                                                                     in
                                                                    uu____17450
                                                                    ::
                                                                    uu____17485
                                                                     in
                                                                    uu____17442
                                                                    ::
                                                                    uu____17447
                                                                     in
                                                                   FStar_List.append
                                                                    uu____17439
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____17436
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____17433
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____17430
                                                              in
                                                           FStar_List.append
                                                             uu____17391
                                                             uu____17427
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____17388
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____17385
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____17382
                                                      in
                                                   let uu____17530 =
                                                     let uu____17531 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17531 g
                                                      in
                                                   (uu____17530, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17565  ->
              fun se  ->
                match uu____17565 with
                | (g,env1) ->
                    let uu____17585 = encode_sigelt env1 se  in
                    (match uu____17585 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17653 =
        match uu____17653 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17690 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17698 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17698
                   then
                     let uu____17703 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17705 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17707 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17703 uu____17705 uu____17707
                   else ());
                  (let uu____17712 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17712 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17730 =
                         let uu____17738 =
                           let uu____17740 =
                             let uu____17742 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17742
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17740  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17738
                          in
                       (match uu____17730 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17762 = FStar_Options.log_queries ()
                                 in
                              if uu____17762
                              then
                                let uu____17765 =
                                  let uu____17767 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17769 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17771 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17767 uu____17769 uu____17771
                                   in
                                FStar_Pervasives_Native.Some uu____17765
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17787 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17797 =
                                let uu____17800 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17800  in
                              FStar_List.append uu____17787 uu____17797  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17812,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17832 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17832 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____17853 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____17853 with | (uu____17880,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17933  ->
              match uu____17933 with
              | (l,uu____17942,uu____17943) ->
                  let uu____17946 =
                    let uu____17958 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17958, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17946))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17991  ->
              match uu____17991 with
              | (l,uu____18002,uu____18003) ->
                  let uu____18006 =
                    let uu____18007 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _18010  -> FStar_SMTEncoding_Term.Echo _18010)
                      uu____18007
                     in
                  let uu____18011 =
                    let uu____18014 =
                      let uu____18015 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____18015  in
                    [uu____18014]  in
                  uu____18006 :: uu____18011))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____18033 =
      let uu____18036 =
        let uu____18037 = FStar_Util.psmap_empty ()  in
        let uu____18052 =
          let uu____18061 = FStar_Util.psmap_empty ()  in (uu____18061, [])
           in
        let uu____18068 =
          let uu____18070 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____18070 FStar_Ident.string_of_lid  in
        let uu____18072 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____18037;
          FStar_SMTEncoding_Env.fvar_bindings = uu____18052;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____18068;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____18072
        }  in
      [uu____18036]  in
    FStar_ST.op_Colon_Equals last_env uu____18033
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____18116 = FStar_ST.op_Bang last_env  in
      match uu____18116 with
      | [] -> failwith "No env; call init first!"
      | e::uu____18144 ->
          let uu___1568_18147 = e  in
          let uu____18148 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1568_18147.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1568_18147.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1568_18147.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1568_18147.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1568_18147.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1568_18147.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1568_18147.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____18148;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1568_18147.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1568_18147.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____18156 = FStar_ST.op_Bang last_env  in
    match uu____18156 with
    | [] -> failwith "Empty env stack"
    | uu____18183::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____18215  ->
    let uu____18216 = FStar_ST.op_Bang last_env  in
    match uu____18216 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____18276  ->
    let uu____18277 = FStar_ST.op_Bang last_env  in
    match uu____18277 with
    | [] -> failwith "Popping an empty stack"
    | uu____18304::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____18341  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____18394  ->
         let uu____18395 = snapshot_env ()  in
         match uu____18395 with
         | (env_depth,()) ->
             let uu____18417 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____18417 with
              | (varops_depth,()) ->
                  let uu____18439 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____18439 with
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
        (fun uu____18497  ->
           let uu____18498 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18498 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18593 = snapshot msg  in () 
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
        | (uu____18639::uu____18640,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1629_18648 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1629_18648.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1629_18648.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1629_18648.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18649 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1635_18676 = elt  in
        let uu____18677 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1635_18676.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1635_18676.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18677;
          FStar_SMTEncoding_Term.a_names =
            (uu___1635_18676.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18697 =
        let uu____18700 =
          let uu____18701 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18701  in
        let uu____18702 = open_fact_db_tags env  in uu____18700 ::
          uu____18702
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18697
  
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
      let uu____18729 = encode_sigelt env se  in
      match uu____18729 with
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
                (let uu____18775 =
                   let uu____18778 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18778
                    in
                 match uu____18775 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18793 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18793
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18823 = FStar_Options.log_queries ()  in
        if uu____18823
        then
          let uu____18828 =
            let uu____18829 =
              let uu____18831 =
                let uu____18833 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18833 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18831  in
            FStar_SMTEncoding_Term.Caption uu____18829  in
          uu____18828 :: decls
        else decls  in
      (let uu____18852 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18852
       then
         let uu____18855 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18855
       else ());
      (let env =
         let uu____18861 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18861 tcenv  in
       let uu____18862 = encode_top_level_facts env se  in
       match uu____18862 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18876 =
               let uu____18879 =
                 let uu____18882 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18882
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18879  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18876)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18915 = FStar_Options.log_queries ()  in
          if uu____18915
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1673_18935 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1673_18935.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1673_18935.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1673_18935.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1673_18935.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1673_18935.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1673_18935.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1673_18935.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1673_18935.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1673_18935.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1673_18935.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18940 =
             let uu____18943 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18943
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18940  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18963 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18963
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
          (let uu____18987 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____18987
           then
             let uu____18990 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____18990
           else ());
          (let env =
             let uu____18998 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____18998
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____19037  ->
                     fun se  ->
                       match uu____19037 with
                       | (g,env2) ->
                           let uu____19057 = encode_top_level_facts env2 se
                              in
                           (match uu____19057 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____19080 =
             encode_signature
               (let uu___1696_19089 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1696_19089.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1696_19089.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1696_19089.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1696_19089.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1696_19089.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1696_19089.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1696_19089.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1696_19089.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1696_19089.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1696_19089.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____19080 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19105 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19105
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____19111 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____19111))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____19139  ->
        match uu____19139 with
        | (decls,fvbs) ->
            ((let uu____19153 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____19153
              then ()
              else
                (let uu____19158 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19158
                 then
                   let uu____19161 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____19161
                 else ()));
             (let env =
                let uu____19169 = get_env name tcenv  in
                FStar_All.pipe_right uu____19169
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____19171 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____19171
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____19185 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____19185
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
        (let uu____19247 =
           let uu____19249 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____19249.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____19247);
        (let env =
           let uu____19251 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____19251 tcenv  in
         let uu____19252 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____19291 = aux rest  in
                 (match uu____19291 with
                  | (out,rest1) ->
                      let t =
                        let uu____19319 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____19319 with
                        | FStar_Pervasives_Native.Some uu____19322 ->
                            let uu____19323 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____19323
                              x.FStar_Syntax_Syntax.sort
                        | uu____19324 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding true;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____19329 =
                        let uu____19332 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1737_19335 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1737_19335.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1737_19335.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____19332 :: out  in
                      (uu____19329, rest1))
             | uu____19340 -> ([], bindings)  in
           let uu____19347 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____19347 with
           | (closing,bindings) ->
               let uu____19374 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____19374, bindings)
            in
         match uu____19252 with
         | (q1,bindings) ->
             let uu____19405 = encode_env_bindings env bindings  in
             (match uu____19405 with
              | (env_decls,env1) ->
                  ((let uu____19427 =
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
                    if uu____19427
                    then
                      let uu____19434 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____19434
                    else ());
                   (let uu____19439 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____19439 with
                    | (phi,qdecls) ->
                        let uu____19460 =
                          let uu____19465 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19465 phi
                           in
                        (match uu____19460 with
                         | (labels,phi1) ->
                             let uu____19482 = encode_labels labels  in
                             (match uu____19482 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19518 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19518
                                    then
                                      let uu____19523 =
                                        let uu____19524 =
                                          let uu____19526 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____19526
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19524
                                         in
                                      [uu____19523]
                                    else []  in
                                  let query_prelude =
                                    let uu____19534 =
                                      let uu____19535 =
                                        let uu____19536 =
                                          let uu____19539 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19546 =
                                            let uu____19549 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19549
                                             in
                                          FStar_List.append uu____19539
                                            uu____19546
                                           in
                                        FStar_List.append env_decls
                                          uu____19536
                                         in
                                      FStar_All.pipe_right uu____19535
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19534
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19559 =
                                      let uu____19567 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19568 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19567,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19568)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19559
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
  